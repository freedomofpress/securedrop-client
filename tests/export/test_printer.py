import unittest
from unittest.mock import MagicMock

from PyQt5.QtCore import QObject, pyqtSignal, pyqtSlot
from PyQt5.QtTest import QSignalSpy

from securedrop_client.export import ExportError, ExportStatus, Printer, Service, getPrinter
from tests.helper import app  # noqa: F401


class PrintingService(QObject):
    """A dummy printing service which responses can be configured for testing purposes."""

    printer_found_ready = pyqtSignal()
    printer_not_found_ready = pyqtSignal(object)

    # allow to wait for response without assuming any response in particular
    response_emitted = pyqtSignal()

    print_failed = pyqtSignal(object)
    print_succeeded = pyqtSignal(object)

    def __init__(self, responses=[Printer.StatusReady]):
        super().__init__()

        self.responses = responses[:]

    def connect_signals(
        self,
        printer_check_requested=None,
        print_requested=None,
    ):

        if print_requested is not None:
            print_requested.connect(self.print)
        if printer_check_requested is not None:
            printer_check_requested.connect(self.check_printer)

    @pyqtSlot()
    def check_printer(self):
        try:
            response = self.responses.pop(0)
            # The printer is unreachable unless it's ready.
            # Note that using the Printer.Status type is merely for convenience and readability.
            if response == Printer.StatusReady:
                self.printer_found_ready.emit()
            else:
                reason = object()  # to comply with the Service API
                self.printer_not_found_ready.emit(reason)
        except IndexError:
            reason = object()
            self.printer_not_found_ready.emit(reason)

        self.response_emitted.emit()


class PrintingServiceClient(QObject):
    """A dummy printing service client to test the dummy printing service.

    Let's make sure our tests rely on reliable tooling!"""

    query_printing_service = pyqtSignal()

    def __init__(self):
        super().__init__()


class Portfolio(QObject):
    """A dummy portfolio that can send documents to be printed for testing purposes."""

    document_sent = pyqtSignal(list)

    def __init__(self):
        super().__init__()


class TestPrintingService(unittest.TestCase):
    def test_printing_service_responds_with_printer_found_ready_by_default(self):
        client = PrintingServiceClient()
        printing_service = PrintingService()  # default responses

        printer_found_ready_emissions = QSignalSpy(printing_service.printer_found_ready)
        printer_not_found_ready_emissions = QSignalSpy(printing_service.printer_not_found_ready)
        self.assertTrue(printer_found_ready_emissions.isValid())
        self.assertTrue(printer_not_found_ready_emissions.isValid())

        printing_service.connect_signals(printer_check_requested=client.query_printing_service)

        client.query_printing_service.emit()  # Act.
        self.assertEqual(1, len(printer_found_ready_emissions))
        self.assertEqual(0, len(printer_not_found_ready_emissions))

    def test_printing_service_responds_as_configured(self):
        client = PrintingServiceClient()
        responses = [
            "not ready",  # whatever
            Printer.StatusReady,
            Printer.StatusReady,
            Printer.StatusUnreachable,  # not Printer.StatusReady
            Printer.StatusReady,
            # nothing else
        ]
        printing_service = PrintingService(responses)  # override default responses
        printer_found_ready_emissions = QSignalSpy(printing_service.printer_found_ready)
        printer_not_found_ready_emissions = QSignalSpy(printing_service.printer_not_found_ready)
        self.assertTrue(printer_found_ready_emissions.isValid())
        self.assertTrue(printer_not_found_ready_emissions.isValid())

        printing_service.connect_signals(printer_check_requested=client.query_printing_service)

        client.query_printing_service.emit()  # Act.
        self.assertEqual(0, len(printer_found_ready_emissions))
        self.assertEqual(1, len(printer_not_found_ready_emissions))

        client.query_printing_service.emit()  # Act again, because we care about the sequence, etc.
        self.assertEqual(1, len(printer_found_ready_emissions))
        self.assertEqual(1, len(printer_not_found_ready_emissions))

        client.query_printing_service.emit()
        self.assertEqual(2, len(printer_found_ready_emissions))
        self.assertEqual(1, len(printer_not_found_ready_emissions))

        client.query_printing_service.emit()
        self.assertEqual(2, len(printer_found_ready_emissions))
        self.assertEqual(2, len(printer_not_found_ready_emissions))

        client.query_printing_service.emit()
        self.assertEqual(3, len(printer_found_ready_emissions))
        self.assertEqual(2, len(printer_not_found_ready_emissions))

        # After all configured responses are consumed, defaults to printer not found ready.
        client.query_printing_service.emit()
        self.assertEqual(3, len(printer_found_ready_emissions))
        self.assertEqual(3, len(printer_not_found_ready_emissions))

        client.query_printing_service.emit()
        self.assertEqual(3, len(printer_found_ready_emissions))
        self.assertEqual(4, len(printer_not_found_ready_emissions))


class TestPrinter(unittest.TestCase):
    def test_printer_is_unique_for_any_given_printing_service(self):
        printing_service = Service()
        printer = getPrinter(printing_service)
        same_printer = getPrinter(printing_service)

        self.assertTrue(
            printer is same_printer,
            "expected successive calls to getPrinter to return the same printer, got different printers",  # noqa: E501
        )

    def test_printer_status_is_unknown_by_default(self):
        printing_service = Service()
        printer = getPrinter(printing_service)

        self.assertEqual(Printer.StatusUnknown, printer.status)

    def test_printer_status_tracks_printing_service_responses_when_connected(self):
        responses = [
            Printer.StatusReady,
            Printer.StatusUnreachable,
            Printer.StatusReady,
        ]
        printing_service = PrintingService(responses)
        printing_service_response = QSignalSpy(printing_service.response_emitted)
        self.assertTrue(printing_service_response.isValid())

        POLLING_INTERVAL = 200  # milliseconds
        # There is a limit to the precision of the timer, but 50ms is plenty to play with.
        FRACTION_OF_POLLING_INTERVAL = 50  # milliseconds
        CHECK_EXECUTION_TIME = 20  # milliseconds

        printer = getPrinter(printing_service, POLLING_INTERVAL)

        self.ensure_that_printer_internals_are_ready_to_process_events(printer, 400)

        # Warming up...
        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected default printer status to be Printer.StatusUnknown, was not.",
        )

        self.assertEqual(
            0,
            len(printing_service_response),
            "Expected printing service to receive no queries before the printer is connected, and emit no responses.",  # noqa: E501
        )

        printer.connect()  # Action!

        # The first query should be issued immediately.
        # After that, the dummy printing service responds blazing fast.
        printing_service_response.wait(CHECK_EXECUTION_TIME)  # milliseconds
        self.assertEqual(
            1,
            len(printing_service_response),
            "Expected exactly 1 query to the printing service, and 1 response immediately after the printer was connected.",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusReady,
            printer.status,
            "Expected printer status to track the last response, did not.",
        )

        # No new queries are issued before the polling interval has elapsed.
        printing_service_response.wait(POLLING_INTERVAL - FRACTION_OF_POLLING_INTERVAL)
        self.assertEqual(
            1,
            len(printing_service_response),
            "Expected no new query, nor response (unchanged total of 1) before the polling interval elapsed.",  # noqa: E501
        )

        # A new query is issued after the polling interval has elapsed,
        # the dummy printing service response is almost instantaneous.
        printing_service_response.wait(FRACTION_OF_POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            2,
            len(printing_service_response),
            "Expected exactly a total of 2 queries, and 2 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusUnreachable,
            printer.status,
            "Expected printer status to track the last response, did not.",
        )

        printing_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            3,
            len(printing_service_response),
            "Expected exactly a total of 3 queries, and 3 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusReady,
            printer.status,
            "Expected printer status to track the last response, did not.",
        )

        printing_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            4,
            len(printing_service_response),
            "Expected exactly a total of 4 queries, and 4 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusUnreachable,
            printer.status,
            "Expected printer status to track the last response, did not.",
        )

    def test_printer_status_stops_tracking_printing_service_responses_when_disconnected(self):
        responses = [
            Printer.StatusReady,
            Printer.StatusUnreachable,
            Printer.StatusReady,
        ]
        printing_service = PrintingService(responses)
        printing_service_response = QSignalSpy(printing_service.response_emitted)
        self.assertTrue(printing_service_response.isValid())

        POLLING_INTERVAL = 100  # milliseconds
        CHECK_EXECUTION_TIME = 20  # milliseconds
        printer = getPrinter(printing_service, POLLING_INTERVAL)

        self.ensure_that_printer_internals_are_ready_to_process_events(printer, 400)

        # Warming up...
        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected default printer status to be Printer.StatusUnknown, was not.",
        )

        self.assertEqual(
            0,
            len(printing_service_response),
            "Expected printing service to receive no queries before the printer is connected, and emit no responses.",  # noqa: E501
        )

        printer.connect()  # Action!

        # The first query should be issued immediately.
        # After that, the dummy printing service responds blazing fast.
        printing_service_response.wait(CHECK_EXECUTION_TIME)  # milliseconds
        self.assertEqual(
            1,
            len(printing_service_response),
            "Expected exactly 1 query to the printing service, and 1 response immediately after the printer was connected.",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusReady,
            printer.status,
            "Expected printer status to track the last response, did not.",
        )

        printer.disconnect()

        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected printer status to become unknown as soon as disconnected.",
        )

        printing_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)  # will time out
        self.assertEqual(
            1,
            len(printing_service_response),
            "Expected no new query to the printing service after disconnection (total 1 query and 1 response)",  # noqa: E501
        )
        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected printer status to remain unknown until reconnected.",
        )

    def test_printer_signals_changes_in_printer_status(self):
        printing_service = PrintingService(["not ready"])

        POLLING_INTERVAL = 200  # milliseconds
        printer = getPrinter(printing_service, POLLING_INTERVAL)

        printer_status_changed_emissions = QSignalSpy(printer.status_changed)
        self.assertTrue(printer_status_changed_emissions.isValid())

        self.ensure_that_printer_internals_are_ready_to_process_events(printer, 400)

        # Warming up...
        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected default printer status to be Printer.StatusUnknown, was not.",
        )
        self.assertEqual(
            1,
            len(printer_status_changed_emissions),
            "Expected printer_status_changed to be emitted when printer is initialized.",
        )

        printing_service.printer_found_ready.emit()
        self.assertEqual(
            Printer.StatusReady,
            printer.status,
            "Expected printer status to become Printer.StatusReady, did not.",
        )
        self.assertEqual(
            2,
            len(printer_status_changed_emissions),
            "Expected printer_status_changed to be emitted, was not.",
        )

        printing_service.printer_found_ready.emit()
        self.assertEqual(
            Printer.StatusReady,
            printer.status,
            "Didn't expect any change in printer status.",
        )
        self.assertEqual(
            2,
            len(printer_status_changed_emissions),
            "Expected printer_status_changed not to be emitted (total count 2), but it was.",
        )

        reason = object()
        printing_service.printer_not_found_ready.emit(reason)
        self.assertEqual(
            Printer.StatusUnreachable,
            printer.status,
            "Expected printer status to become Printer.StatusUnreachable, did not.",
        )
        self.assertEqual(
            3,
            len(printer_status_changed_emissions),
            "Expected printer_status_changed to be emitted, was not.",
        )

        # This last segment is admittedly awkward. We want to make sure that
        # the signal is emitted when pausing the printer. Even though the printer connection
        # is not the point of this test, we do have to connect to be able to disconnect it.
        #
        # The connection triggers a query to the printer_service. To ensure that
        # connecting the printer doesn't have any visible side-effects, the dummy service
        # is configured to respond that the printer wasn't found ready.
        printer.connect()
        printer.disconnect()
        printer_status_changed_emissions.wait(POLLING_INTERVAL)
        self.assertEqual(
            Printer.StatusUnknown,
            printer.status,
            "Expected printer status to become Printer.StatusUnknown as soon as disconnected, was not.",  # noqa: E501
        )
        self.assertEqual(
            4,
            len(printer_status_changed_emissions),
            "Expected printer_status_changed to be emitted, was not.",
        )

    def test_printer_last_error_returns_none_by_default(self):
        printing_service = PrintingService()
        printer = getPrinter(printing_service)

        assert printer.last_error is None

    def test_printer_last_error_returns_the_last_service_error_when_printer_not_found_ready(
        self,
    ):
        printing_service = PrintingService()
        printer_not_found_ready_emissions = QSignalSpy(printing_service.printer_not_found_ready)
        assert printer_not_found_ready_emissions.isValid()

        printer = getPrinter(printing_service)
        error = ExportError(ExportStatus.PRINTER_NOT_FOUND)
        expected_error = error

        printing_service.printer_not_found_ready.emit(error)
        printer_not_found_ready_emissions.wait(50)

        self.assertEqual(expected_error, printer.last_error)

        # another round

        error = ExportError(ExportStatus.CALLED_PROCESS_ERROR)
        expected_error = error

        printing_service.printer_not_found_ready.emit(error)
        printer_not_found_ready_emissions.wait(50)

        self.assertEqual(expected_error, printer.last_error)

    def test_printer_last_error_returns_the_last_service_error_when_print_fails(self):
        printing_service = PrintingService()
        print_failed_emissions = QSignalSpy(printing_service.print_failed)
        assert print_failed_emissions.isValid()

        printer = getPrinter(printing_service)
        error = ExportError(ExportStatus.PRINTER_NOT_FOUND)
        expected_error = error

        printing_service.print_failed.emit(error)
        print_failed_emissions.wait(50)

        self.assertEqual(expected_error, printer.last_error)

        # another round

        error = ExportError(ExportStatus.CALLED_PROCESS_ERROR)
        expected_error = error

        printing_service.print_failed.emit(error)
        print_failed_emissions.wait(50)

        self.assertEqual(expected_error, printer.last_error)

    def test_printer_allows_to_enqueue_printing_job(self):
        portfolio = Portfolio()

        printing_service = Service()
        print_method = MagicMock()
        printing_service.print = print_method

        printer = getPrinter(printing_service)
        printer.enqueue_job_on(portfolio.document_sent)

        portfolio.document_sent.emit(["my_document"])

        # The printing service is not up-to-date on the printing queue terminology.
        print_method.assert_called_once_with(["my_document"])

    def test_printer_signals_when_printing_jobs_are_enqueued_successfully(self):
        printing_service = Service()
        printer = getPrinter(printing_service)

        job_done_emissions = QSignalSpy(printer.job_done)
        job_failed_emissions = QSignalSpy(printer.job_failed)
        self.assertTrue(job_done_emissions.isValid())
        self.assertTrue(job_failed_emissions.isValid())

        # The printing service is not up-to-date on the printing queue terminology.
        printing_service.print_succeeded.emit()

        self.assertEqual(
            1,
            len(job_done_emissions),
            "Expected printer to a emit job_done signal when the printing service reports success.",
        )
        self.assertEqual(
            0,
            len(job_failed_emissions),
            f"Expected printer to emit no job_failed signal when the printing service reports success, got {len(job_failed_emissions)}.",  # noqa: E501
        )

    def test_printer_signals_when_printing_jobs_enqueueing_fails(self):
        printing_service = Service()
        printer = getPrinter(printing_service)

        job_done_emissions = QSignalSpy(printer.job_done)
        job_failed_emissions = QSignalSpy(printer.job_failed)
        self.assertTrue(job_done_emissions.isValid())
        self.assertTrue(job_failed_emissions.isValid())

        # The printing service is not up-to-date on the printing queue terminology.
        printing_service.print_failed.emit("a good reason")

        self.assertEqual(
            1,
            len(job_failed_emissions),
            "Expected printer to emit a job_failed signal when the printing service reports a failure.",  # noqa: E501
        )
        self.assertEqual(
            0,
            len(job_done_emissions),
            f"Expected printer to emit no job_done signal when the printing service reports a failure, got {len(job_done_emissions)}.",  # noqa: E501
        )

    def ensure_that_printer_internals_are_ready_to_process_events(
        self, printer, max_waiting_time_in_milliseconds
    ):
        """Give a little bit of time to the state machines to start.

        All QStateMachine instances require Qt's event loop to be processing
        events before being considered to be fully started and running.

        This is a bit sad and an implementation detail, but testing
        components that depend on Qt's event loop is like that."""
        poller_started = QSignalSpy(printer._poller.started)
        cache_started = QSignalSpy(printer._cache.started)

        # these are max waiting times, not required pauses
        poller_started.wait(int(max_waiting_time_in_milliseconds / 2))
        cache_started.wait(int(max_waiting_time_in_milliseconds / 2))

        self.assertTrue(
            printer._poller.isRunning(),
            f"Expected the printer poller to be running after {max_waiting_time_in_milliseconds}ms. Abort the test.",  # noqa: E501
        )
        self.assertTrue(
            printer._cache.isRunning(),
            f"Expected the printer cache to be running after {max_waiting_time_in_milliseconds}ms. Abort the test.",  # noqa: E501
        )


class TestPrinterDeprecatedInterface(unittest.TestCase):
    def test_performs_one_check_when_registered_signal_is_emitted(self):
        client = PrintingServiceClient()
        printing_service = PrintingService()
        printer = getPrinter(printing_service)

        response_emitted_emissions = QSignalSpy(printing_service.response_emitted)
        self.assertTrue(response_emitted_emissions.isValid())

        printer.check_status_once_on(client.query_printing_service)
        client.query_printing_service.emit()  # Act.

        self.assertEqual(
            1,
            len(response_emitted_emissions),
            "Expected service to emit a response as a result of being queried.",
        )
