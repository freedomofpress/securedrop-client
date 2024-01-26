from securedrop_client.export_status import ExportError, ExportStatus
from securedrop_client.gui.conversation import ExportTranscriptDialog
from tests.helper import app  # noqa: F401


def test_TranscriptDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.ExportTranscriptDialog._show_starting_instructions"
    )

    export_transcript_dialog = ExportTranscriptDialog(
        mocker.MagicMock(), "transcript.txt", "/some/path/transcript.txt"
    )

    _show_starting_instructions_fn.assert_called_once_with()
    assert export_transcript_dialog.passphrase_form.isHidden()


def test_TranscriptDialog_init_sanitizes_filename(mocker):
    secure_qlabel = mocker.patch(
        "securedrop_client.gui.conversation.export.file_dialog.SecureQLabel"
    )
    mocker.patch("securedrop_client.gui.widgets.QVBoxLayout.addWidget")
    filename = '<script>alert("boom!");</script>'

    ExportTranscriptDialog(mocker.MagicMock(), filename, "/some/path/transcript.txt")

    secure_qlabel.assert_any_call(filename, wordwrap=False, max_length=260)


def test_TranscriptDialog__show_starting_instructions(mocker, export_transcript_dialog):
    export_transcript_dialog._show_starting_instructions()

    # transcript.txt comes from the export_transcript_dialog fixture
    assert (
        export_transcript_dialog.header.text() == "Preparing to export:"
        "<br />"
        '<span style="font-weight:normal">transcript.txt</span>'
    )
    assert (
        export_transcript_dialog.body.text()
        == "<h2>Understand the risks before exporting files</h2>"
        "<b>Malware</b>"
        "<br />"
        "This workstation lets you open files securely. If you open files on another "
        "computer, any embedded malware may spread to your computer or network. If you are "
        "unsure how to manage this risk, please print the file, or contact your "
        "administrator."
        "<br /><br />"
        "<b>Anonymity</b>"
        "<br />"
        "Files submitted by sources may contain information or hidden metadata that "
        "identifies who they are. To protect your sources, please consider redacting files "
        "before working with them on network-connected computers."
    )
    assert not export_transcript_dialog.header.isHidden()
    assert not export_transcript_dialog.header_line.isHidden()
    assert export_transcript_dialog.error_details.isHidden()
    assert not export_transcript_dialog.body.isHidden()
    assert export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog___show_passphrase_request_message(mocker, export_transcript_dialog):
    export_transcript_dialog._show_passphrase_request_message()

    assert export_transcript_dialog.header.text() == "Enter passphrase for USB drive"
    assert not export_transcript_dialog.header.isHidden()
    assert export_transcript_dialog.header_line.isHidden()
    assert export_transcript_dialog.error_details.isHidden()
    assert export_transcript_dialog.body.isHidden()
    assert not export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__show_passphrase_request_message_again(mocker, export_transcript_dialog):
    export_transcript_dialog._show_passphrase_request_message_again()

    assert export_transcript_dialog.header.text() == "Enter passphrase for USB drive"
    assert (
        export_transcript_dialog.error_details.text()
        == "The passphrase provided did not work. Please try again."
    )
    assert export_transcript_dialog.body.isHidden()
    assert not export_transcript_dialog.header.isHidden()
    assert export_transcript_dialog.header_line.isHidden()
    assert not export_transcript_dialog.error_details.isHidden()
    assert export_transcript_dialog.body.isHidden()
    assert not export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__show_success_message(mocker, export_transcript_dialog):
    export_transcript_dialog._show_success_message()

    assert export_transcript_dialog.header.text() == "Export successful"
    assert (
        export_transcript_dialog.body.text()
        == "Remember to be careful when working with files outside of your Workstation machine."
    )
    assert not export_transcript_dialog.header.isHidden()
    assert not export_transcript_dialog.header_line.isHidden()
    assert export_transcript_dialog.error_details.isHidden()
    assert not export_transcript_dialog.body.isHidden()
    assert export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__show_insert_usb_message(mocker, export_transcript_dialog):
    export_transcript_dialog._show_insert_usb_message()

    assert export_transcript_dialog.header.text() == "Insert encrypted USB drive"
    assert (
        export_transcript_dialog.body.text()
        == "Please insert one of the export drives provisioned specifically "
        "for the SecureDrop Workstation."
    )
    assert not export_transcript_dialog.header.isHidden()
    assert not export_transcript_dialog.header_line.isHidden()
    assert export_transcript_dialog.error_details.isHidden()
    assert not export_transcript_dialog.body.isHidden()
    assert export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__show_insert_encrypted_usb_message(mocker, export_transcript_dialog):
    export_transcript_dialog._show_insert_encrypted_usb_message()

    assert export_transcript_dialog.header.text() == "Insert encrypted USB drive"
    assert (
        export_transcript_dialog.error_details.text()
        == "Either the drive is not encrypted or there is something else wrong with it."
    )
    assert (
        export_transcript_dialog.body.text()
        == "Please insert one of the export drives provisioned specifically for the SecureDrop "
        "Workstation."
    )
    assert not export_transcript_dialog.header.isHidden()
    assert not export_transcript_dialog.header_line.isHidden()
    assert not export_transcript_dialog.error_details.isHidden()
    assert not export_transcript_dialog.body.isHidden()
    assert export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__show_generic_error_message(mocker, export_transcript_dialog):
    export_transcript_dialog.error_status = "mock_error_status"

    export_transcript_dialog._show_generic_error_message()

    assert export_transcript_dialog.header.text() == "Export failed"
    assert (
        export_transcript_dialog.body.text()
        == "mock_error_status: See your administrator for help."
    )
    assert not export_transcript_dialog.header.isHidden()
    assert not export_transcript_dialog.header_line.isHidden()
    assert export_transcript_dialog.error_details.isHidden()
    assert not export_transcript_dialog.body.isHidden()
    assert export_transcript_dialog.passphrase_form.isHidden()
    assert not export_transcript_dialog.continue_button.isHidden()
    assert not export_transcript_dialog.cancel_button.isHidden()


def test_TranscriptDialog__export_transcript(mocker, export_transcript_dialog):
    device = mocker.MagicMock()
    device.export = mocker.MagicMock()
    export_transcript_dialog._device = device
    export_transcript_dialog.passphrase_field.text = mocker.MagicMock(
        return_value="mock_passphrase"
    )

    export_transcript_dialog._export_transcript()

    device.export.assert_called_once_with(["/some/path/transcript.txt"], "mock_passphrase")


def test_TranscriptDialog__on_export_preflight_check_succeeded(mocker, export_transcript_dialog):
    export_transcript_dialog._show_passphrase_request_message = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    export_transcript_dialog._on_export_preflight_check_succeeded(ExportStatus.DEVICE_LOCKED)

    export_transcript_dialog._show_passphrase_request_message.assert_not_called()
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_passphrase_request_message
    )


def test_TranscriptDialog__on_export_preflight_check_succeeded_when_continue_enabled(
    mocker, export_transcript_dialog
):
    export_transcript_dialog._show_passphrase_request_message = mocker.MagicMock()
    export_transcript_dialog.continue_button.setEnabled(True)

    export_transcript_dialog._on_export_preflight_check_succeeded(ExportStatus.DEVICE_LOCKED)

    export_transcript_dialog._show_passphrase_request_message.assert_called_once_with()


def test_TranscriptDialog__on_export_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, export_transcript_dialog
):
    assert not export_transcript_dialog.continue_button.isEnabled()
    export_transcript_dialog._on_export_preflight_check_succeeded(ExportStatus.DEVICE_LOCKED)
    assert export_transcript_dialog.continue_button.isEnabled()


def test_TranscriptDialog__on_export_preflight_check_succeeded_enabled_after_preflight_failure(
    mocker, export_transcript_dialog
):
    assert not export_transcript_dialog.continue_button.isEnabled()
    export_transcript_dialog._on_export_preflight_check_failed(mocker.MagicMock())
    assert export_transcript_dialog.continue_button.isEnabled()


def test_TranscriptDialog__on_export_preflight_check_failed(mocker, export_transcript_dialog):
    export_transcript_dialog._update_dialog = mocker.MagicMock()

    error = ExportError("mock_error_status")
    export_transcript_dialog._on_export_preflight_check_failed(error)

    export_transcript_dialog._update_dialog.assert_called_with("mock_error_status")


def test_TranscriptDialog__on_export_succeeded(mocker, export_transcript_dialog):
    export_transcript_dialog._show_success_message = mocker.MagicMock()

    export_transcript_dialog._on_export_succeeded(ExportStatus.SUCCESS_EXPORT)

    export_transcript_dialog._show_success_message.assert_called_once_with()


def test_TranscriptDialog__on_export_failed(mocker, export_transcript_dialog):
    export_transcript_dialog._update_dialog = mocker.MagicMock()

    error = ExportError("mock_error_status")
    export_transcript_dialog._on_export_failed(error)

    export_transcript_dialog._update_dialog.assert_called_with("mock_error_status")


def test_TranscriptDialog__update_dialog_when_status_is_USB_NOT_CONNECTED(
    mocker, export_transcript_dialog
):
    export_transcript_dialog._show_insert_usb_message = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_transcript_dialog._update_dialog(ExportStatus.NO_DEVICE_DETECTED)
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_insert_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=True)
    export_transcript_dialog._update_dialog(ExportStatus.NO_DEVICE_DETECTED)
    export_transcript_dialog._show_insert_usb_message.assert_called_once_with()


def test_TranscriptDialog__update_dialog_when_status_is_BAD_PASSPHRASE(
    mocker, export_transcript_dialog
):
    export_transcript_dialog._show_passphrase_request_message_again = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_transcript_dialog._update_dialog(ExportStatus.ERROR_UNLOCK_LUKS)
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_passphrase_request_message_again
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=True)
    export_transcript_dialog._update_dialog(ExportStatus.ERROR_UNLOCK_LUKS)
    export_transcript_dialog._show_passphrase_request_message_again.assert_called_once_with()


def test_TranscriptDialog__update_dialog_when_status_DISK_ENCRYPTION_NOT_SUPPORTED_ERROR(
    mocker, export_transcript_dialog
):
    export_transcript_dialog._show_insert_encrypted_usb_message = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_transcript_dialog._update_dialog(ExportStatus.INVALID_DEVICE_DETECTED)
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_insert_encrypted_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=True)
    export_transcript_dialog._update_dialog(ExportStatus.INVALID_DEVICE_DETECTED)
    export_transcript_dialog._show_insert_encrypted_usb_message.assert_called_once_with()


def test_TranscriptDialog__update_dialog_when_status_is_CALLED_PROCESS_ERROR(
    mocker, export_transcript_dialog
):
    export_transcript_dialog._show_generic_error_message = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_transcript_dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_generic_error_message
    )
    assert export_transcript_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=True)
    export_transcript_dialog._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_transcript_dialog._show_generic_error_message.assert_called_once_with()
    assert export_transcript_dialog.error_status == ExportStatus.CALLED_PROCESS_ERROR


def test_TranscriptDialog__update_dialog_when_status_is_unknown(mocker, export_transcript_dialog):
    export_transcript_dialog._show_generic_error_message = mocker.MagicMock()
    export_transcript_dialog.continue_button = mocker.MagicMock()
    export_transcript_dialog.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_transcript_dialog._update_dialog("Some Unknown Error Status")
    export_transcript_dialog.continue_button.clicked.connect.assert_called_once_with(
        export_transcript_dialog._show_generic_error_message
    )
    assert export_transcript_dialog.error_status == "Some Unknown Error Status"

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_transcript_dialog.continue_button, "isEnabled", return_value=True)
    export_transcript_dialog._update_dialog("Some Unknown Error Status")
    export_transcript_dialog._show_generic_error_message.assert_called_once_with()
    assert export_transcript_dialog.error_status == "Some Unknown Error Status"
