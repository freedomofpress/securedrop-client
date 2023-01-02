import warnings
from typing import Callable, NewType, Optional

from PyQt5.QtCore import QObject, QState, QStateMachine, QTimer, pyqtSignal, pyqtSlot

from .cli import Error as CLIError
from .service import Service

DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS = 2000


class Disk(QObject):
    """Allows to export files to an ecrypted disk and track its availability."""

    status_changed = pyqtSignal()
    export_done = pyqtSignal()
    export_failed = pyqtSignal(str)

    client_connected = pyqtSignal()
    last_client_disconnected = pyqtSignal()

    Status = NewType("Status", str)
    StatusUnknown = Status("unknown-isw32")
    StatusLUKSEncrypted = Status("luks-encrypted-8563d")
    StatusUnreachable = Status("unreachable-ofbu4")

    def __init__(
        self,
        export_service: Service,
        polling_interval_in_milliseconds: int = DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS,
    ) -> None:
        super().__init__()

        self._connected_clients = 0
        self._export_service = export_service
        self._poller = _Poller(polling_interval_in_milliseconds)
        self._cache = _StatusCache(self._export_service)
        self._last_error: Optional[CLIError] = None

        # Accept that the status is unknown if we don't watch the disk for a bit.
        self._cache.clear_on(self._poller.paused.entered)
        self._cache.on_change_emit(self.status_changed)

        # This is a blocking call, which is no good.
        # self._poller.poll_by(lambda: self._export_service.check_disk())
        # Alternatively, by taking advantage of the export service features to loosen coupling:
        self._export_service.connect_signals(disk_check_requested=self._poller.polling.entered)

        self._poller.wait_on(self._export_service.luks_encrypted_disk_found)
        self._poller.wait_on(self._export_service.luks_encrypted_disk_not_found)

        self._poller.start_on(self.client_connected)
        self._poller.pause_on(self.last_client_disconnected)

        self._export_service.luks_encrypted_disk_not_found.connect(
            lambda error: self._on_luks_encrypted_disk_not_found(error)
        )
        self._export_service.export_failed.connect(self._on_export_failed)
        self._export_service.export_succeeded.connect(self._on_export_succeeded)

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

    def export_on(self, signal: pyqtSignal) -> None:
        """Allow to export files, in a thread-safe manner."""
        self._export_service.connect_signals(export_requested=signal)

    def check_status_once_on(self, signal: pyqtSignal) -> None:
        warnings.warn(
            "check_status_once_on must not be used for nwe features, use the connect method instead",  # noqa: E501
            DeprecationWarning,
            stacklevel=2,
        )

        self._export_service.connect_signals(disk_check_requested=signal)

    @pyqtSlot()
    def _on_luks_encrypted_disk_not_found(self, error: CLIError) -> None:
        self._last_error = error

    @pyqtSlot()
    def _on_export_succeeded(self) -> None:
        self.export_done.emit()

    @pyqtSlot(object)
    def _on_export_failed(self, error: CLIError) -> None:
        self._last_error = error
        self.export_failed.emit("")  # FIXME Decide what errors to emit.


class _StatusCache(QStateMachine):
    """A cache that holds the information available about the status of the export disk.

    Paste the following state chart in https://mermaid.live for
    a visual representation of the behavior implemented by this class!
    stateDiagram-v2
      [*] --> unknown
      unknown --> luks_encrypted: export_service.luks_encrypted_disk_found
      unknown --> unreachable: export_service.luks_encrypted_disk_not_found

      luks_encrypted --> luks_unreachable: export_service.luks_encrypted_disk_not_found
      luks_encrypted --> unknown: registered_clearing_signal_emitted

      unreachable --> luks_encrypted: export_service.luks_encrypted_disk_found
      unreachable --> unknown: registered_clearing_signal_emitted
    """

    def __init__(self, export_service: Service) -> None:
        super().__init__()

        self._service = export_service
        self._status = Disk.StatusUnknown

        # Declare the state chart described in the docstring.
        # See https://doc.qt.io/qt-5/statemachine-api.html
        #
        # This is a very declarative exercise.

        self._unknown = QState()
        self._luks_encrypted = QState()
        self._unreachable = QState()

        self._unknown.addTransition(self._service.luks_encrypted_disk_found, self._luks_encrypted)
        self._unknown.addTransition(self._service.luks_encrypted_disk_not_found, self._unreachable)

        self._luks_encrypted.addTransition(
            self._service.luks_encrypted_disk_not_found, self._unreachable
        )
        self._unreachable.addTransition(
            self._service.luks_encrypted_disk_found, self._luks_encrypted
        )

        # The transitions to the unknown state are created
        # when clearing signals are connected.

        self.addState(self._unknown)
        self.addState(self._luks_encrypted)
        self.addState(self._unreachable)

        self.setInitialState(self._unknown)

        self._unknown.entered.connect(self._on_unknown_state_entered)
        self._luks_encrypted.entered.connect(self._on_luks_encrypted_state_entered)
        self._unreachable.entered.connect(self._on_unreachable_state_entered)

        self.start()

    def clear_on(self, signal: pyqtSignal) -> None:
        """Allow the cache to be cleared (status == Disk.UnknownStatus) when signal is emitted.

        Register a clearing signal."""
        self._luks_encrypted.addTransition(signal, self._unknown)
        self._unreachable.addTransition(signal, self._unknown)

    def on_change_emit(self, signal: pyqtSignal) -> None:
        """Allow a signal to be emitted when the value of the cache changes."""
        self._unknown.entered.connect(signal)
        self._luks_encrypted.entered.connect(signal)
        self._unreachable.entered.connect(signal)

    @property
    def status(self) -> Disk.Status:
        return self._status

    @pyqtSlot()
    def _on_unknown_state_entered(self) -> None:
        self._status = Disk.StatusUnknown

    @pyqtSlot()
    def _on_luks_encrypted_state_entered(self) -> None:
        self._status = Disk.StatusLUKSEncrypted

    @pyqtSlot()
    def _on_unreachable_state_entered(self) -> None:
        self._status = Disk.StatusUnreachable


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

    def start_on(self, signal: pyqtSignal) -> None:
        """Allow polling to be started, in a thread-safe manner.

        Register a starting signal."""
        self.paused.addTransition(signal, self._started)

    def pause_on(self, signal: pyqtSignal) -> None:
        """Allow polling to be paused, in a thread-safe manner.

        Register a pausing signal."""
        self._started.addTransition(signal, self.paused)

    def wait_on(self, signal: pyqtSignal) -> None:
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


# Store disks to prevent concurrent access to the export service. See getDisk.
_disks: dict[int, Disk] = {}


def getDisk(
    export_service: Service,
    polling_interval_in_milliseconds: int = DEFAULT_POLLING_INTERVAL_IN_MILLISECONDS,
) -> Disk:
    """Return a disk with a specific configuration.

    All calls to this function with the same configuration return the same disk instance."""
    global _disks

    # Only create one disk by export service,
    # to prevent unnecessary concurrent access to the export service.
    disk_id = id(export_service)

    disk = _disks.get(disk_id, None)
    if not disk:
        disk = Disk(export_service, polling_interval_in_milliseconds)
        _disks[disk_id] = disk

    return disk
