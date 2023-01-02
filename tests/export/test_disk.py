import unittest
from unittest.mock import MagicMock

from PyQt5.QtCore import QObject, pyqtSignal, pyqtSlot
from PyQt5.QtTest import QSignalSpy

from securedrop_client.export import Disk, ExportError, ExportStatus, Service, getDisk
from tests.helper import app  # noqa: F401


class ExportService(QObject):
    """A dummy export service which responses can be configured for testing purposes."""

    luks_encrypted_disk_found = pyqtSignal()
    luks_encrypted_disk_not_found = pyqtSignal(object)

    # allow to wait for response without assuming any response in particular
    response_emitted = pyqtSignal()

    export_failed = pyqtSignal(object)
    export_succeeded = pyqtSignal(object)

    def __init__(self, responses=[Disk.StatusLUKSEncrypted]):
        super().__init__()

        self.responses = responses

    def connect_signals(
        self,
        disk_check_requested=None,
        export_requested=None,
    ):

        if export_requested is not None:
            export_requested.connect(self.export)
        if disk_check_requested is not None:
            disk_check_requested.connect(self.check_disk)

    @pyqtSlot()
    def check_disk(self):
        try:
            response = self.responses.pop(0)
            # The disk is unreachable unless it's LUKS-encrypted.
            # Note that using the Disk.Status type is merely for convenience and readability.
            if response == Disk.StatusLUKSEncrypted:
                self.luks_encrypted_disk_found.emit()
            else:
                reason = object()  # to comply with the Service API
                self.luks_encrypted_disk_not_found.emit(reason)
        except IndexError:
            reason = object()
            self.luks_encrypted_disk_not_found.emit(reason)

        self.response_emitted.emit()


class ExportServiceClient(QObject):
    """A dummy export service client to test the dummy export service.

    Let's make sure our tests rely on reliable tooling!"""

    query_export_service = pyqtSignal()

    def __init__(self):
        super().__init__()


class Portfolio(QObject):
    """A dummy portfolio that can send files to be exported for testing purposes."""

    file_sent = pyqtSignal(list)

    def __init__(self):
        super().__init__()


class TestExportService(unittest.TestCase):
    def test_export_service_responds_with_luks_encrypted_disk_found_by_default(self):
        client = ExportServiceClient()
        export_service = ExportService()  # default responses

        luks_encrypted_disk_found_emissions = QSignalSpy(export_service.luks_encrypted_disk_found)
        luks_encrypted_disk_not_found = QSignalSpy(export_service.luks_encrypted_disk_not_found)
        self.assertTrue(luks_encrypted_disk_found_emissions.isValid())
        self.assertTrue(luks_encrypted_disk_not_found.isValid())

        export_service.connect_signals(disk_check_requested=client.query_export_service)

        client.query_export_service.emit()  # Act.
        self.assertEqual(1, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(0, len(luks_encrypted_disk_not_found))

    def test_export_service_responds_as_configured(self):
        client = ExportServiceClient()
        responses = [
            "not LUKS-encrypted",  # whatever
            Disk.StatusLUKSEncrypted,
            Disk.StatusLUKSEncrypted,
            Disk.StatusUnreachable,  # not Disk.StatusLUKSEncrypted
            Disk.StatusLUKSEncrypted,
            # nothing else
        ]
        export_service = ExportService(responses)  # override default responses
        luks_encrypted_disk_found_emissions = QSignalSpy(export_service.luks_encrypted_disk_found)
        luks_encrypted_disk_not_found = QSignalSpy(export_service.luks_encrypted_disk_not_found)
        self.assertTrue(luks_encrypted_disk_found_emissions.isValid())
        self.assertTrue(luks_encrypted_disk_not_found.isValid())

        export_service.connect_signals(disk_check_requested=client.query_export_service)

        client.query_export_service.emit()  # Act.
        self.assertEqual(0, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(1, len(luks_encrypted_disk_not_found))

        client.query_export_service.emit()  # Act again, because we care about the sequence, etc.
        self.assertEqual(1, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(1, len(luks_encrypted_disk_not_found))

        client.query_export_service.emit()
        self.assertEqual(2, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(1, len(luks_encrypted_disk_not_found))

        client.query_export_service.emit()
        self.assertEqual(2, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(2, len(luks_encrypted_disk_not_found))

        client.query_export_service.emit()
        self.assertEqual(3, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(2, len(luks_encrypted_disk_not_found))

        # After all configured responses are consumed, defaults to LUKS-encrypted disk not found.
        client.query_export_service.emit()
        self.assertEqual(3, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(3, len(luks_encrypted_disk_not_found))

        client.query_export_service.emit()
        self.assertEqual(3, len(luks_encrypted_disk_found_emissions))
        self.assertEqual(4, len(luks_encrypted_disk_not_found))


class TestDisk(unittest.TestCase):
    def test_disk_is_unique_for_any_given_export_service(self):
        export_service = Service()
        disk = getDisk(export_service)
        same_disk = getDisk(export_service)

        self.assertTrue(
            disk is same_disk,
            "expected successive calls to getDisk to return the same disk, got different disks",  # noqa: E501
        )

    def test_disk_status_is_unknown_by_default(self):
        export_service = Service()
        disk = getDisk(export_service)

        self.assertEqual(Disk.StatusUnknown, disk.status)

    def test_disk_status_tracks_export_service_responses_when_connected(self):
        responses = [
            Disk.StatusLUKSEncrypted,
            Disk.StatusUnreachable,
            Disk.StatusLUKSEncrypted,
        ]
        export_service = ExportService(responses)
        export_service_response = QSignalSpy(export_service.response_emitted)
        self.assertTrue(export_service_response.isValid())

        POLLING_INTERVAL = 200  # milliseconds
        # There is a limit to the precision of the timer, but 50ms is plenty to play with.
        FRACTION_OF_POLLING_INTERVAL = 50  # milliseconds
        CHECK_EXECUTION_TIME = 20  # milliseconds

        disk = getDisk(export_service, POLLING_INTERVAL)

        self.ensure_that_disk_internals_are_ready_to_process_events(disk, 400)

        # Warming up...
        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected default disk status to be Disk.StatusUnknown, was not.",
        )

        self.assertEqual(
            0,
            len(export_service_response),
            "Expected export service to receive no queries before the disk is connected, and emit no responses.",  # noqa: E501
        )

        disk.connect()  # Action!

        # The first query should be issued immediately.
        # After that, the dummy export service responds blazing fast.
        export_service_response.wait(CHECK_EXECUTION_TIME)  # milliseconds
        self.assertEqual(
            1,
            len(export_service_response),
            "Expected exactly 1 query to the export service, and 1 response immediately after the disk was connected.",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusLUKSEncrypted,
            disk.status,
            "Expected disk status to track the last response, did not.",
        )

        # No new queries are issued before the polling interval has elapsed.
        export_service_response.wait(POLLING_INTERVAL - FRACTION_OF_POLLING_INTERVAL)
        self.assertEqual(
            1,
            len(export_service_response),
            "Expected no new query, nor response (unchanged total of 1) before the polling interval elapsed.",  # noqa: E501
        )

        # A new query is issued after the polling interval has elapsed,
        # the dummy export service response is almost instantaneous.
        export_service_response.wait(FRACTION_OF_POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            2,
            len(export_service_response),
            "Expected exactly a total of 2 queries, and 2 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusUnreachable,
            disk.status,
            "Expected disk status to track the last response, did not.",
        )

        export_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            3,
            len(export_service_response),
            "Expected exactly a total of 3 queries, and 3 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusLUKSEncrypted,
            disk.status,
            "Expected disk status to track the last response, did not.",
        )

        export_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)
        self.assertEqual(
            4,
            len(export_service_response),
            "Expected exactly a total of 4 queries, and 4 responses after the polling interval elapsed.",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusUnreachable,
            disk.status,
            "Expected disk status to track the last response, did not.",
        )

    def test_disk_last_error_returns_none_by_default(self):
        export_service = ExportService()
        disk = getDisk(export_service)

        assert disk.last_error is None

    def test_disk_last_error_returns_the_last_service_error_when_luks_encrypted_disk_not_found(
        self,
    ):
        export_service = ExportService()
        luks_encrypted_disk_not_found_emissions = QSignalSpy(
            export_service.luks_encrypted_disk_not_found
        )
        assert luks_encrypted_disk_not_found_emissions.isValid()

        disk = getDisk(export_service)
        error = ExportError(ExportStatus.USB_NOT_CONNECTED)
        expected_error = error

        export_service.luks_encrypted_disk_not_found.emit(error)
        luks_encrypted_disk_not_found_emissions.wait(50)

        self.assertEqual(expected_error, disk.last_error)

        # another round

        error = ExportError(ExportStatus.CALLED_PROCESS_ERROR)
        expected_error = error

        export_service.luks_encrypted_disk_not_found.emit(error)
        luks_encrypted_disk_not_found_emissions.wait(50)

        self.assertEqual(expected_error, disk.last_error)

    def test_disk_last_error_returns_the_last_service_error_when_export_fails(self):
        export_service = ExportService()
        export_failed_emissions = QSignalSpy(export_service.export_failed)
        assert export_failed_emissions.isValid()

        disk = getDisk(export_service)
        error = ExportError(ExportStatus.BAD_PASSPHRASE)
        expected_error = error

        export_service.export_failed.emit(error)
        export_failed_emissions.wait(50)

        self.assertEqual(expected_error, disk.last_error)

        # another round

        error = ExportError(ExportStatus.CALLED_PROCESS_ERROR)
        expected_error = error

        export_service.export_failed.emit(error)
        export_failed_emissions.wait(50)

        self.assertEqual(expected_error, disk.last_error)

    def test_disk_status_stops_tracking_export_service_responses_when_disconnected(self):
        responses = [
            Disk.StatusLUKSEncrypted,
            Disk.StatusUnreachable,
            Disk.StatusLUKSEncrypted,
        ]
        export_service = ExportService(responses)
        export_service_response = QSignalSpy(export_service.response_emitted)
        self.assertTrue(export_service_response.isValid())

        POLLING_INTERVAL = 100  # milliseconds
        CHECK_EXECUTION_TIME = 20  # milliseconds
        disk = getDisk(export_service, POLLING_INTERVAL)

        self.ensure_that_disk_internals_are_ready_to_process_events(disk, 400)

        # Warming up...
        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected default disk status to be Disk.StatusUnknown, was not.",
        )

        self.assertEqual(
            0,
            len(export_service_response),
            "Expected export service to receive no queries before the disk is connected, and emit no responses.",  # noqa: E501
        )

        disk.connect()  # Action!

        # The first query should be issued immediately.
        # After that, the dummy export service responds blazing fast.
        export_service_response.wait(CHECK_EXECUTION_TIME)  # milliseconds
        self.assertEqual(
            1,
            len(export_service_response),
            "Expected exactly 1 query to the export service, and 1 response immediately after the disk was connected.",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusLUKSEncrypted,
            disk.status,
            "Expected disk status to track the last response, did not.",
        )

        disk.disconnect()

        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected disk status to become unknown as soon as disconnected.",
        )

        export_service_response.wait(POLLING_INTERVAL + CHECK_EXECUTION_TIME)  # will time out
        self.assertEqual(
            1,
            len(export_service_response),
            "Expected no new query to the export service after disconnection (total 1 query and 1 response)",  # noqa: E501
        )
        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected disk status to remain unknown until reconnected.",
        )

    def test_disk_signals_changes_in_disk_status(self):
        export_service = ExportService(["not LUKS-encrypted"])

        POLLING_INTERVAL = 200  # milliseconds
        disk = getDisk(export_service, POLLING_INTERVAL)

        disk_status_changed_emissions = QSignalSpy(disk.status_changed)
        self.assertTrue(disk_status_changed_emissions.isValid())

        self.ensure_that_disk_internals_are_ready_to_process_events(disk, 400)

        # Warming up...
        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected default disk status to be Disk.StatusUnknown, was not.",
        )
        self.assertEqual(
            1,
            len(disk_status_changed_emissions),
            "Expected disk_status_changed to be emitted when disk is initialized.",
        )

        export_service.luks_encrypted_disk_found.emit()
        self.assertEqual(
            Disk.StatusLUKSEncrypted,
            disk.status,
            "Expected disk status to become Disk.StatusLUKSEncrypted, did not.",
        )
        self.assertEqual(
            2,
            len(disk_status_changed_emissions),
            "Expected disk_status_changed to be emitted, was not.",
        )

        export_service.luks_encrypted_disk_found.emit()
        self.assertEqual(
            Disk.StatusLUKSEncrypted,
            disk.status,
            "Didn't expect any change in disk status.",
        )
        self.assertEqual(
            2,
            len(disk_status_changed_emissions),
            "Expected disk_status_changed not to be emitted (total count 2), but it was.",
        )

        reason = object()
        export_service.luks_encrypted_disk_not_found.emit(reason)
        self.assertEqual(
            Disk.StatusUnreachable,
            disk.status,
            "Expected disk status to become Disk.StatusUnreachable, did not.",
        )
        self.assertEqual(
            3,
            len(disk_status_changed_emissions),
            "Expected disk_status_changed to be emitted, was not.",
        )

        # This last segment is admittedly awkward. We want to make sure that
        # the signal is emitted when pausing the disk. Even though the disk connection
        # is not the point of this test, we do have to connect to be able to disconnect it.
        #
        # The connection triggers a query to the disk_service. To ensure that
        # connecting the disk doesn't have any visible side-effects, the dummy service
        # is configured to respond that the disk wasn't found LUKS-encrypted.
        disk.connect()
        disk.disconnect()
        disk_status_changed_emissions.wait(POLLING_INTERVAL)
        self.assertEqual(
            Disk.StatusUnknown,
            disk.status,
            "Expected disk status to become Disk.StatusUnknown as soon as disconnected, was not.",  # noqa: E501
        )
        self.assertEqual(
            4,
            len(disk_status_changed_emissions),
            "Expected disk_status_changed to be emitted, was not.",
        )

    def test_disk_allows_to_export(self):
        portfolio = Portfolio()

        export_service = Service()
        export_method = MagicMock()
        export_service.export = export_method

        disk = getDisk(export_service)
        disk.export_on(portfolio.file_sent)

        portfolio.file_sent.emit(["my_file"])

        export_method.assert_called_once_with(["my_file"])

    def test_disk_signals_when_export_is_successful(self):
        export_service = Service()
        disk = getDisk(export_service)

        export_done_emissions = QSignalSpy(disk.export_done)
        export_failed_emissions = QSignalSpy(disk.export_failed)
        self.assertTrue(export_done_emissions.isValid())
        self.assertTrue(export_failed_emissions.isValid())

        export_service.export_succeeded.emit()

        self.assertEqual(
            1,
            len(export_done_emissions),
            "Expected disk to a emit export_done signal when the export service reports success.",
        )
        self.assertEqual(
            0,
            len(export_failed_emissions),
            f"Expected disk to emit no export_failed signal when the export service reports success, got {len(export_failed_emissions)}.",  # noqa: E501
        )

    def test_disk_signals_when_export_fails(self):
        export_service = Service()
        disk = getDisk(export_service)

        export_done_emissions = QSignalSpy(disk.export_done)
        export_failed_emissions = QSignalSpy(disk.export_failed)
        self.assertTrue(export_done_emissions.isValid())
        self.assertTrue(export_failed_emissions.isValid())

        export_service.export_failed.emit("a good reason")

        self.assertEqual(
            1,
            len(export_failed_emissions),
            "Expected disk to emit a job_failed signal when the export service reports a failure.",
        )
        self.assertEqual(
            0,
            len(export_done_emissions),
            f"Expected disk to emit no export_done signal when the export service reports a failure, got {len(export_done_emissions)}.",  # noqa: E501
        )

    def ensure_that_disk_internals_are_ready_to_process_events(
        self, disk, max_waiting_time_in_milliseconds
    ):
        """Give a little bit of time to the state machines to start.

        All QStateMachine instances require Qt's event loop to be processing
        events before being considered to be fully started and running.

        This is a bit sad and an implementation detail, but testing
        components that depend on Qt's event loop is like that."""
        poller_started = QSignalSpy(disk._poller.started)
        cache_started = QSignalSpy(disk._cache.started)

        # these are max waiting times, not required pauses
        poller_started.wait(int(max_waiting_time_in_milliseconds / 2))
        cache_started.wait(int(max_waiting_time_in_milliseconds / 2))

        self.assertTrue(
            disk._poller.isRunning(),
            f"Expected the disk poller to be running after {max_waiting_time_in_milliseconds}ms. Abort the test.",  # noqa: E501
        )
        self.assertTrue(
            disk._cache.isRunning(),
            f"Expected the disk cache to be running after {max_waiting_time_in_milliseconds}ms. Abort the test.",  # noqa: E501
        )


class TestDiskDeprecatedInterface(unittest.TestCase):
    def test_performs_one_check_when_registered_signal_is_emitted(self):
        client = ExportServiceClient()
        export_service = ExportService()
        disk = getDisk(export_service)

        response_emitted_emissions = QSignalSpy(export_service.response_emitted)
        self.assertTrue(response_emitted_emissions.isValid())

        disk.check_status_once_on(client.query_export_service)
        client.query_export_service.emit()  # Act.

        self.assertEqual(
            1,
            len(response_emitted_emissions),
            "Expected service to emit a response as a result of being queried.",
        )
