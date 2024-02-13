from securedrop_client.export_status import ExportError, ExportStatus
from securedrop_client.gui.conversation import PrintDialog
from tests.helper import app  # noqa: F401


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
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintDialog__show_insert_usb_message(mocker, print_dialog):
    print_dialog._show_insert_usb_message()

    assert print_dialog.header.text() == "Connect USB printer"
    assert print_dialog.body.text() == "Please connect your printer to a USB port."
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintDialog__show_generic_error_message(mocker, print_dialog):
    print_dialog.error_status = "mock_error_status"

    print_dialog._show_generic_error_message()

    assert print_dialog.header.text() == "Printing failed"
    assert print_dialog.body.text() == "mock_error_status: See your administrator for help."
    assert not print_dialog.header.isHidden()
    assert not print_dialog.header_line.isHidden()
    assert print_dialog.error_details.isHidden()
    assert not print_dialog.body.isHidden()
    assert not print_dialog.continue_button.isHidden()
    assert not print_dialog.cancel_button.isHidden()


def test_PrintDialog__print_file(mocker, print_dialog):
    print_dialog.close = mocker.MagicMock()

    print_dialog._print_file()

    print_dialog._device.print.assert_called_once_with(print_dialog.filepaths)


def test_PrintDialog__on_print_preflight_check_succeeded(mocker, print_dialog):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    print_dialog._on_print_preflight_check_succeeded(ExportStatus.PRINT_PREFLIGHT_SUCCESS)

    print_dialog._print_file.assert_not_called()
    print_dialog.continue_button.clicked.connect.assert_called_once_with(print_dialog._print_file)


def test_PrintDialog__on_print_preflight_check_succeeded_when_continue_enabled(
    mocker, print_dialog
):
    print_dialog._print_file = mocker.MagicMock()
    print_dialog.continue_button.setEnabled(True)

    print_dialog._on_print_preflight_check_succeeded(ExportStatus.PRINT_PREFLIGHT_SUCCESS)

    print_dialog._print_file.assert_called_once_with()


def test_PrintDialog__on_print_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, print_dialog
):
    assert not print_dialog.continue_button.isEnabled()
    print_dialog._on_print_preflight_check_succeeded(ExportStatus.PRINT_PREFLIGHT_SUCCESS)
    assert print_dialog.continue_button.isEnabled()


def test_PrintDialog__on_print_preflight_check_succeeded_enabled_after_preflight_failure(
    mocker, print_dialog
):
    assert not print_dialog.continue_button.isEnabled()
    print_dialog._on_print_preflight_check_failed(mocker.MagicMock())
    assert print_dialog.continue_button.isEnabled()


def test_PrintDialog__on_print_preflight_check_failed_when_status_is_PRINTER_NOT_FOUND(
    mocker, print_dialog
):
    print_dialog._show_insert_usb_message = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.ERROR_PRINTER_NOT_FOUND))
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_insert_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=True)
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.ERROR_PRINTER_NOT_FOUND))
    print_dialog._show_insert_usb_message.assert_called_once_with()


def test_PrintDialog__on_print_preflight_check_failed_when_status_is_ERROR_PRINTER_URI(
    mocker, print_dialog
):
    print_dialog._show_generic_error_message = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.ERROR_PRINTER_URI))
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_generic_error_message
    )
    assert print_dialog.error_status == ExportStatus.ERROR_PRINTER_URI

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=True)
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.ERROR_PRINTER_URI))
    print_dialog._show_generic_error_message.assert_called_once_with()
    assert print_dialog.error_status == ExportStatus.ERROR_PRINTER_URI


def test_PrintDialog__on_print_preflight_check_failed_when_status_is_CALLED_PROCESS_ERROR(
    mocker, print_dialog
):
    print_dialog._show_generic_error_message = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.CALLED_PROCESS_ERROR))
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_generic_error_message
    )
    assert print_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=True)
    print_dialog._on_print_preflight_check_failed(ExportError(ExportStatus.CALLED_PROCESS_ERROR))
    print_dialog._show_generic_error_message.assert_called_once_with()
    assert print_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR


def test_PrintDialog__on_print_preflight_check_failed_when_status_is_unknown(mocker, print_dialog):
    print_dialog._show_generic_error_message = mocker.MagicMock()
    print_dialog.continue_button = mocker.MagicMock()
    print_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_dialog._on_print_preflight_check_failed(ExportError("Some Unknown Error Status"))
    print_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_dialog._show_generic_error_message
    )
    assert print_dialog.error_status == "Some Unknown Error Status"

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_dialog.continue_button, "isEnabled", return_value=True)
    print_dialog._on_print_preflight_check_failed(ExportError("Some Unknown Error Status"))
    print_dialog._show_generic_error_message.assert_called_once_with()
    assert print_dialog.error_status == "Some Unknown Error Status"
