import warnings
from typing import Callable, NewType, Optional

from PyQt5.QtCore import (
    QObject,
    QState,
    QStateMachine,
    QTimer,
    pyqtBoundSignal,
    pyqtSignal,
    pyqtSlot,
)

from .cli import Error as CLIError
from .service import Service

DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS = 2000


class Printer(QObject):
    """Allows to enqueue printing jobs and track the status of the printing queue.

    It can be treated like a printer, but technically speaking it only interfaces with
    a printing queue, not an actual printer. Success or failure enqueing jobs can be tracked,
    and is the best proxy we currently have to tracking the outcome of printing operations."""

    status_changed = pyqtSignal()
    job_done = pyqtSignal()
    job_failed = pyqtSignal()

    client_connected = pyqtSignal()
    last_client_disconnected = pyqtSignal()

    Status = NewType("Status", str)
    StatusUnknown = Status("unknown-sf5fd")
    StatusReady = Status("ready-83jf3")
    StatusUnreachable = Status("unreachable-120a0")

    def __init__(
        self,
        printing_service: Service,
        polling_interval_in_milliseconds: int = DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS,
    ) -> None:
        super().__init__()

        self._connected_clients = 0
        self._printing_service = printing_service
        self._poller = _Poller(polling_interval_in_milliseconds)
        self._cache = _StatusCache(self._printing_service)
        self._last_error: Optional[CLIError] = None

        # Accept that the status is unknown if we don't watch the printer for a bit.
        self._cache.clear_on(self._poller.paused.entered)
        self._cache.on_change_emit(self.status_changed)

        # This is a blocking call, which is no good.
        # self._poller.poll_by(lambda: self._printing_service.check_printer())
        # Alternatively, by taking advantage of the printing service features to loosen coupling:
        self._printing_service.connect_signals(printer_check_requested=self._poller.polling.entered)

        self._poller.wait_on(self._printing_service.printer_not_found_ready)
        self._poller.wait_on(self._printing_service.printer_found_ready)

        self._poller.start_on(self.client_connected)
        self._poller.pause_on(self.last_client_disconnected)

        # The printing service is not up-to-date on the printing queue terminology.
        self._printing_service.printer_not_found_ready.connect(
            lambda error: self._on_printer_not_found_ready(error)
        )
        self._printing_service.print_failed.connect(self._on_job_enqueuing_failed)
        self._printing_service.print_succeeded.connect(self._on_job_enqueued)

    @property
    def status(self) -> Status:
        return self._cache.status

    @property
    def last_error(self) -> Optional[CLIError]:
        return self._last_error  # FIXME Returning the CLIError type is an abstraction leak.

    @pyqtSlot()
    def connect(self) -> None:
        self._connected_clients += 1
        self.client_connected.emit()

    @pyqtSlot()
    def disconnect(self) -> None:
        self._connected_clients -= 1
        if self._connected_clients < 1:
            self.last_client_disconnected.emit()

    def enqueue_job_on(self, signal: pyqtBoundSignal) -> None:
        """Allow to enqueue printing jobs, in a thread-safe manner."""
        self._printing_service.connect_signals(print_requested=signal)

    def check_status_once_on(self, signal: pyqtBoundSignal) -> None:
        warnings.warn(
            "check_status_once_on must not be used for new features, use the connect method instead",  # noqa: E501
            DeprecationWarning,
            stacklevel=2,
        )

        self._printing_service.connect_signals(printer_check_requested=signal)

    @pyqtSlot()
    def _on_printer_not_found_ready(self, error: CLIError) -> None:
        self._last_error = error

    @pyqtSlot()
    def _on_job_enqueued(self) -> None:
        self.job_done.emit()

    @pyqtSlot(object)
    def _on_job_enqueuing_failed(self, error: CLIError) -> None:
        self._last_error = error
        self.job_failed.emit()


class _StatusCache(QStateMachine):
    """A cache that holds the information available about the status of the printing pipeline.

    Paste the following state chart in https://mermaid.live for
    a visual representation of the behavior implemented by this class!
    stateDiagram-v2
      [*] --> unknown
      unknown --> ready: printing_service.printer_found_ready
      unknown --> unreachable: printing_service.printer_not_found_ready

      ready --> unreachable: printing_service.printer_not_found_ready
      ready --> unknown: registered_clearing_signal_emitted

      unreachable --> ready: printing_service.printer_found_ready
      unreachable --> unknown: registered_clearing_signal_emitted
    """

    def __init__(self, printing_service: Service) -> None:
        super().__init__()

        self._service = printing_service
        self._status = Printer.StatusUnknown

        # Declare the state chart described in the docstring.
        # See https://doc.qt.io/qt-5/statemachine-api.html
        #
        # This is a very declarative exercise.

        self._unknown = QState()
        self._ready = QState()
        self._unreachable = QState()

        self._unknown.addTransition(self._service.printer_found_ready, self._ready)
        self._unknown.addTransition(self._service.printer_not_found_ready, self._unreachable)

        self._ready.addTransition(self._service.printer_not_found_ready, self._unreachable)
        self._unreachable.addTransition(self._service.printer_found_ready, self._ready)

        # The transitions to the unknown state are created
        # when clearing signals are connected.

        self.addState(self._unknown)
        self.addState(self._ready)
        self.addState(self._unreachable)

        self.setInitialState(self._unknown)

        self._unknown.entered.connect(self._on_unknown_state_entered)
        self._ready.entered.connect(self._on_ready_state_entered)
        self._unreachable.entered.connect(self._on_unreachable_state_entered)

        self.start()

    def clear_on(self, signal: pyqtBoundSignal) -> None:
        """Allow the cache to be cleared (status == Printer.UnknownStatus) when signal is emitted.

        Register a clearing signal."""
        self._ready.addTransition(signal, self._unknown)
        self._unreachable.addTransition(signal, self._unknown)

    def on_change_emit(self, signal: pyqtBoundSignal) -> None:
        """Allow a signal to be emitted whe the value of the cache changes."""
        self._unknown.entered.connect(signal)
        self._ready.entered.connect(signal)
        self._unreachable.entered.connect(signal)

    @property
    def status(self) -> Printer.Status:
        return self._status

    @pyqtSlot()
    def _on_unknown_state_entered(self) -> None:
        self._status = Printer.StatusUnknown

    @pyqtSlot()
    def _on_ready_state_entered(self) -> None:
        self._status = Printer.StatusReady

    @pyqtSlot()
    def _on_unreachable_state_entered(self) -> None:
        self._status = Printer.StatusUnreachable


class _Poller(QStateMachine):
    """Allow a function to ge called repeatedly, with a delay between calls.

    Paste the following state chart in https://mermaid.live for
    a visual representation of the behavior implemented by this class!
    stateDiagram-v2
      [*] --> paused

      state started {
          [*] --> polling
          polling --> waiting: registered_waiting_signal_emitted
          waiting --> polling: polling_delay_timer.timeout
      }

      paused --> started: registered_starting_signal_emitted
      started --> paused: registered_pausing_signal_emitted
    """

    def __init__(self, polling_interval_in_milliseconds: int) -> None:
        super().__init__()

        self._polling_delay_timer = QTimer()
        self._polling_delay_timer.setInterval(polling_interval_in_milliseconds)

        # Declare the state chart described in the docstring.
        # See https://doc.qt.io/qt-5/statemachine-api.html
        #
        # This is a very declarative exercise.
        # The public state names are part of the API of this class.

        self.paused = QState()
        self._started = QState()
        self.polling = QState(self._started)
        self._waiting = QState(self._started)

        # The transition from polling to waiting are created
        # when waiting signals are registered.

        self._waiting.addTransition(self._polling_delay_timer.timeout, self.polling)

        # The transitions from paused to started (resp. started to paused)
        # are created when starting (resp. pausing) signals are registered.

        self.addState(self.paused)
        self.addState(self._started)
        self.setInitialState(self.paused)
        self._started.setInitialState(self.polling)

        self._waiting.entered.connect(self._polling_delay_timer.start)
        self.polling.entered.connect(self._polling_delay_timer.stop)

        self.start()  # start the state machine, not polling!

    def start_on(self, signal: pyqtBoundSignal) -> None:
        """Allow polling to be started, in a thread-safe manner.

        Register a starting signal."""
        self.paused.addTransition(signal, self._started)

    def pause_on(self, signal: pyqtBoundSignal) -> None:
        """Allow polling to be paused, in a thread-safe manner.

        Register a pausing signal."""
        self._started.addTransition(signal, self.paused)

    def wait_on(self, signal: pyqtBoundSignal) -> None:
        """Allow to signal that a given polling event is done, in a thread-safe manner.

        Register a waiting signal."""
        self.polling.addTransition(signal, self._waiting)
        signal.connect(self._polling_delay_timer.start)

    def poll_by(self, callback: Callable[[], None]) -> None:
        """Allow a function to ge called repeatedly, with a delay between calls."""
        # It would be nice to connect a signal, but I didn't find how
        # to allow registering a signal that requires arguments without
        # the closure.
        self.polling.entered.connect(lambda: callback())  # pragma: nocover


# Store printers to prevent concurrent access to the printing service. See getPrinter.
_printers: dict[int, Printer] = {}


def getPrinter(
    printing_service: Service,
    polling_interval_in_milliseconds: int = DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS,
) -> Printer:
    """Return a printer with a specific configuration.

    All calls to this function with the same configuration return the same printer instance."""
    global _printers

    # Only create one printer by printing service,
    # to prevent unnecessary concurrent access to the printing service.
    printer_id = id(printing_service)

    printer = _printers.get(printer_id, None)
    if not printer:
        printer = Printer(printing_service, polling_interval_in_milliseconds)
        _printers[printer_id] = printer

    return printer


def clearPrinter(
    export_service: Service,
) -> None:
    global _printers

    # See getPrinter
    printer_id = id(export_service)
    if printer_id in _printers:
        del _printers[printer_id]
