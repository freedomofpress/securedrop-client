import pytest

from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.conversation import PrintDialog


def _assert_is_ready_continue_state(print_dialog):
    """
    Helper. Asserts dialog displays "ready to continue"
    state attributes after successful preflight call.
    """
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def _assert_is_error_state(print_dialog):
    """
    Helper. Assert dialog displays error state attributes.
    """
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.PrintDialog._show_starting_instructions"
    )

    PrintDialog(mocker.MagicMock(), "mock.jpg", ["/mock/path/to/file"])

    _show_starting_instructions_fn.assert_called_once_with()


def test_PrintDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch(
        "securedrop_client.gui.conversation.export.print_dialog.SecureQLabel"
    )
    filename = '<script>alert("boom!");</script>'

    PrintDialog(mocker.MagicMock(), filename, ["/mock/path/to/file"])

    secure_qlabel.assert_any_call(filename, wordwrap=False, max_length=260)


# The print_dialog fixture takes an indirect parameter (must be formatted in a list).
# In this case, that parameter is the string that should be returned by a mock qrexec
# command, or None if no string is needed (testing dialog initialization without
# mocking any qrexec calls). This allows us to manipulate the print_dialog._device
# to test print_dialog behaviour, rather than invoking dialog callbacks directly.
# See conftest.py.
@pytest.mark.parametrize("print_dialog", [None], indirect=True)
def test_PrintDialog__show_starting_instructions(mocker, print_dialog):
    print_dialog._show_starting_instructions()

    # file123.jpg comes from the print_dialog fixture
    assert (
        print_dialog.header.text() == "Preparing to print:"
        "<br />"
        '<span style="font-weight:normal">file123.jpg</span>'
    )
    assert (
        print_dialog.body.text() == "<h2>Managing printout risks</h2>"
        "<b>QR codes and web addresses</b>"
        "<br />"
        "Never type in and open web addresses or scan QR codes contained in printed "
        "documents without taking security precautions. If you are unsure how to "
        "manage this risk, please contact your administrator."
        "<br /><br />"
        "<b>Printer dots</b>"
        "<br />"
        "Any part of a printed page may contain identifying information "
        "invisible to the naked eye, such as printer dots. Please carefully "
        "consider this risk when working with or publishing scanned printouts."
    )
    _assert_is_ready_continue_state(print_dialog)


@pytest.mark.parametrize("print_dialog", [None], indirect=True)
def test_PrintDialog__show_insert_usb_message(mocker, print_dialog):
    print_dialog._show_insert_usb_message()

    assert print_dialog.header.text() == "Connect USB printer"
    assert print_dialog.body.text() == "Please connect your printer to a USB port."

    _assert_is_ready_continue_state(print_dialog)


@pytest.mark.parametrize("print_dialog", [None], indirect=True)
def test_PrintDialog__show_error_message(mocker, print_dialog):
    print_dialog.status = ExportStatus.ERROR_UNPRINTABLE_TYPE
    print_dialog._show_error_message()

    assert print_dialog.header.text() == "Printing failed"
    assert print_dialog.body.text() == (
        f"{ExportStatus.ERROR_UNPRINTABLE_TYPE.value}: "
        f"{print_dialog.unprintable_type_error_message}"
    )
    _assert_is_error_state(print_dialog)


@pytest.mark.parametrize("print_dialog", [None], indirect=True)
def test_PrintDialog__print_file(mocker, print_dialog):
    print_dialog.close = mocker.MagicMock()
    print_dialog._device.print = mocker.MagicMock()

    print_dialog._print_file()

    print_dialog._device.print.assert_called_once_with(print_dialog.filepaths)


@pytest.mark.parametrize(
    "print_dialog", [ExportStatus.PRINT_PREFLIGHT_SUCCESS.value], indirect=True
)
def test_PrintDialog__on_print_preflight_check_succeeded(mocker, print_dialog):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    print_dialog._device._on_print_preflight_complete()

    print_dialog._print_file.assert_not_called()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(print_dialog._print_file)


@pytest.mark.parametrize(
    "print_dialog", [ExportStatus.PRINT_PREFLIGHT_SUCCESS.value], indirect=True
)
def test_PrintDialog__on_print_preflight_check_succeeded_when_continue_enabled_starts_print(
    mocker, print_dialog
):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(True)

    print_dialog._device._on_print_preflight_complete()
    print_dialog._print_file.assert_called_once_with()


@pytest.mark.parametrize(
    "print_dialog",
    [
        ExportStatus.PRINT_PREFLIGHT_SUCCESS.value,
        ExportStatus.ERROR_PRINTER_INSTALL.value,
        ExportStatus.ERROR_PRINTER_NOT_FOUND.value,
    ],
    indirect=True,
)
def test_PrintDialog_continue_button_enabled_after_preflight(mocker, print_dialog):
    """
    Whether or not the background print preflight was a success or a failure,
    the Continue button should be disabled (check running in background),
    then enabled (check has completed and user clicks Continue to see the result).
    Test with success and failure statuses.
    """
    assert not print_dialog.continue_button.isEnabled()
    print_dialog._device._on_print_preflight_complete()
    assert print_dialog.continue_button.isEnabled()


@pytest.mark.parametrize(
    "print_dialog",
    [
        ExportStatus.ERROR_PRINTER_DRIVER_UNAVAILABLE.value,
        ExportStatus.ERROR_MULTIPLE_PRINTERS_FOUND.value,
        ExportStatus.ERROR_PRINTER_NOT_SUPPORTED.value,
        ExportStatus.ERROR_PRINTER_INSTALL.value,
        ExportStatus.ERROR_PRINTER_URI.value,
    ],
    indirect=True,
)
def test_PrintDialog__on_print_preflight_check_failed_shows_error(mocker, print_dialog):
    """
    Ensure preflight error responses result in the dialog displaying
    a helpful message. Parametrized argument is
    passed to print_dialog fixture; see conftest.py.
    """
    print_dialog._show_error_message = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(False)
    print_dialog.continue_button.clicked = mocker.MagicMock()

    # When the Continue button is disabled, finishing a preflight check will
    # enable the Continue button and connect the click handler to an error message,
    # but will not yet display the message (user has to click).
    print_dialog._device._on_print_preflight_complete()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_error_message
    )

    # When the continue button is enabled, ensure clicking it displays the error message
    print_dialog.continue_button.setEnabled(True)
    print_dialog._device._on_print_preflight_complete()
    print_dialog._show_error_message.assert_called_once_with()


@pytest.mark.parametrize(
    "print_dialog", [ExportStatus.ERROR_PRINTER_NOT_FOUND.value], indirect=True
)
def test_PrintDialog__on_print_preflight_check_failed_no_printer_shows_connect_printer_prompt(
    mocker, print_dialog
):
    print_dialog._show_insert_usb_message = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(False)
    print_dialog.continue_button.clicked = mocker.MagicMock()

    # When the Continue button is disabled, finishing a preflight check will
    # enable the Continue button and connect the click handler to an error message,
    # but will not yet display the message (user has to click).
    print_dialog._device._on_print_preflight_complete()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_insert_usb_message
    )
    assert print_dialog.status == ExportStatus.ERROR_PRINTER_NOT_FOUND

    # When the continue button is enabled, ensure clicking it shows next instructions
    print_dialog.continue_button.setEnabled(True)
    print_dialog._device._on_print_preflight_complete()
    print_dialog._show_insert_usb_message.assert_called_once_with()

    _assert_is_ready_continue_state(print_dialog)


@pytest.mark.parametrize("print_dialog", [ExportStatus.CALLED_PROCESS_ERROR.value], indirect=True)
def test_PrintDialog__on_print_preflight_check_failed_when_status_is_CALLED_PROCESS_ERROR(
    mocker, print_dialog
):
    print_dialog._show_error_message = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(False)
    print_dialog.continue_button.clicked = mocker.MagicMock()

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._device._on_print_preflight_complete()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_error_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    print_dialog.continue_button.setEnabled(True)
    print_dialog._device._on_print_preflight_complete()
    print_dialog._show_error_message.assert_called_once_with()
    assert print_dialog.status == ExportStatus.CALLED_PROCESS_ERROR

    _assert_is_error_state(print_dialog)


@pytest.mark.parametrize("print_dialog", ["Some Unknown Error Status"], indirect=True)
def test_PrintDialog__on_print_preflight_check_failed_when_status_is_unknown(mocker, print_dialog):
    print_dialog._show_error_message = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(False)
    print_dialog.continue_button.clicked = mocker.MagicMock()

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._device._on_print_preflight_complete()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_error_message
    )
    assert print_dialog.status == ExportStatus.UNEXPECTED_RETURN_STATUS

    # When the continue button is enabled, ensure next instructions are shown
    print_dialog.continue_button.setEnabled(True)
    print_dialog._device._on_print_preflight_complete()
    print_dialog._show_error_message.assert_called_once_with()
    assert print_dialog.status == ExportStatus.UNEXPECTED_RETURN_STATUS

    _assert_is_error_state(print_dialog)
