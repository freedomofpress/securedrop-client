from securedrop_client.export import ExportError, ExportStatus
from securedrop_client.gui.conversation import PrintTranscriptDialog
from tests.helper import app  # noqa: F401


def test_PrintTranscriptDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.PrintTranscriptDialog._show_starting_instructions"
    )

    PrintTranscriptDialog(mocker.MagicMock(), "conversation.txt", "/some/path/conversation.txt")

    _show_starting_instructions_fn.assert_called_once_with()


def test_PrintTranscriptDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch(
        "securedrop_client.gui.conversation.export.print_dialog.SecureQLabel"
    )
    filename = '<script>alert("boom!");</script>'

    PrintTranscriptDialog(mocker.MagicMock(), filename, "/some/path/conversation.txt")

    secure_qlabel.assert_any_call(filename, wordwrap=False, max_length=260)


def test_PrintTranscriptDialog__show_starting_instructions(mocker, print_transcript_dialog):
    print_transcript_dialog._show_starting_instructions()

    # conversation.txt comes from the print_transcript_dialog fixture
    assert (
        print_transcript_dialog.header.text() == "Preparing to print:"
        "<br />"
        '<span style="font-weight:normal">conversation.txt</span>'
    )
    assert (
        print_transcript_dialog.body.text() == "<h2>Managing printout risks</h2>"
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
    assert not print_transcript_dialog.header.isHidden()
    assert not print_transcript_dialog.header_line.isHidden()
    assert print_transcript_dialog.error_details.isHidden()
    assert not print_transcript_dialog.body.isHidden()
    assert not print_transcript_dialog.continue_button.isHidden()
    assert not print_transcript_dialog.cancel_button.isHidden()


def test_PrintTranscriptDialog__show_insert_usb_message(mocker, print_transcript_dialog):
    print_transcript_dialog._show_insert_usb_message()

    assert print_transcript_dialog.header.text() == "Connect USB printer"
    assert print_transcript_dialog.body.text() == "Please connect your printer to a USB port."
    assert not print_transcript_dialog.header.isHidden()
    assert not print_transcript_dialog.header_line.isHidden()
    assert print_transcript_dialog.error_details.isHidden()
    assert not print_transcript_dialog.body.isHidden()
    assert not print_transcript_dialog.continue_button.isHidden()
    assert not print_transcript_dialog.cancel_button.isHidden()


def test_PrintTranscriptDialog__show_generic_error_message(mocker, print_transcript_dialog):
    print_transcript_dialog.error_status = "mock_error_status"

    print_transcript_dialog._show_generic_error_message()

    assert print_transcript_dialog.header.text() == "Printing failed"
    assert (
        print_transcript_dialog.body.text() == "mock_error_status: See your administrator for help."
    )
    assert not print_transcript_dialog.header.isHidden()
    assert not print_transcript_dialog.header_line.isHidden()
    assert print_transcript_dialog.error_details.isHidden()
    assert not print_transcript_dialog.body.isHidden()
    assert not print_transcript_dialog.continue_button.isHidden()
    assert not print_transcript_dialog.cancel_button.isHidden()


def test_PrintTranscriptDialog__print_transcript(mocker, print_transcript_dialog):
    print_transcript_dialog.close = mocker.MagicMock()

    print_transcript_dialog._print_transcript()

    print_transcript_dialog.close.assert_called_once_with()


def test_PrintTranscriptDialog__on_print_preflight_check_succeeded(mocker, print_transcript_dialog):
    print_transcript_dialog._print_transcript = mocker.MagicMock()
    print_transcript_dialog.continue_button = mocker.MagicMock()
    print_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=False)

    print_transcript_dialog._on_print_preflight_check_succeeded()

    print_transcript_dialog._print_transcript.assert_not_called()
    print_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_transcript_dialog._print_transcript
    )


def test_PrintTranscriptDialog__on_print_preflight_check_succeeded_when_continue_enabled(
    mocker, print_transcript_dialog
):
    print_transcript_dialog._print_transcript = mocker.MagicMock()
    print_transcript_dialog.continue_button.setEnabled(True)

    print_transcript_dialog._on_print_preflight_check_succeeded()

    print_transcript_dialog._print_transcript.assert_called_once_with()


def test_PrintTranscriptDialog__on_print_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, print_transcript_dialog
):
    assert not print_transcript_dialog.continue_button.isEnabled()
    print_transcript_dialog._on_print_preflight_check_succeeded()
    assert print_transcript_dialog.continue_button.isEnabled()


def test_PrintTranscriptDialog__on_print_preflight_check_succeeded_enabled_after_preflight_failure(
    mocker, print_transcript_dialog
):
    assert not print_transcript_dialog.continue_button.isEnabled()
    print_transcript_dialog._on_print_preflight_check_failed(mocker.MagicMock())
    assert print_transcript_dialog.continue_button.isEnabled()


def test_PrintTranscriptDialog__on_print_preflight_check_failed_when_status_is_PRINTER_NOT_FOUND(
    mocker, print_transcript_dialog
):
    print_transcript_dialog._show_insert_usb_message = mocker.MagicMock()
    print_transcript_dialog.continue_button = mocker.MagicMock()
    print_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.PRINTER_NOT_FOUND)
    )
    print_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_transcript_dialog._show_insert_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=True)
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.PRINTER_NOT_FOUND)
    )
    print_transcript_dialog._show_insert_usb_message.assert_called_once_with()


def test_PrintTranscriptDialog__on_print_preflight_check_failed_when_status_is_MISSING_PRINTER_URI(
    mocker, print_transcript_dialog
):
    print_transcript_dialog._show_generic_error_message = mocker.MagicMock()
    print_transcript_dialog.continue_button = mocker.MagicMock()
    print_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.MISSING_PRINTER_URI)
    )
    print_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_transcript_dialog._show_generic_error_message
    )
    assert print_transcript_dialog.error_status == ExportStatus.MISSING_PRINTER_URI

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=True)
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.MISSING_PRINTER_URI)
    )
    print_transcript_dialog._show_generic_error_message.assert_called_once_with()
    assert print_transcript_dialog.error_status == ExportStatus.MISSING_PRINTER_URI


def test_PrintTranscriptDialog__on_print_preflight_check_failed_when_status_is_CALLED_PROCESS_ERROR(
    mocker, print_transcript_dialog
):
    print_transcript_dialog._show_generic_error_message = mocker.MagicMock()
    print_transcript_dialog.continue_button = mocker.MagicMock()
    print_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.CALLED_PROCESS_ERROR)
    )
    print_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_transcript_dialog._show_generic_error_message
    )
    assert print_transcript_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=True)
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError(ExportStatus.CALLED_PROCESS_ERROR)
    )
    print_transcript_dialog._show_generic_error_message.assert_called_once_with()
    assert print_transcript_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR


def test_PrintTranscriptDialog__on_print_preflight_check_failed_when_status_is_unknown(
    mocker, print_transcript_dialog
):
    print_transcript_dialog._show_generic_error_message = mocker.MagicMock()
    print_transcript_dialog.continue_button = mocker.MagicMock()
    print_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError("Some Unknown Error Status")
    )
    print_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        print_transcript_dialog._show_generic_error_message
    )
    assert print_transcript_dialog.error_status == "Some Unknown Error Status"

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(print_transcript_dialog.continue_button, "isEnabled", return_value=True)
    print_transcript_dialog._on_print_preflight_check_failed(
        ExportError("Some Unknown Error Status")
    )
    print_transcript_dialog._show_generic_error_message.assert_called_once_with()
    assert print_transcript_dialog.error_status == "Some Unknown Error Status"
