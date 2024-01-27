from securedrop_client.export_status import ExportError, ExportStatus
from securedrop_client.gui.conversation import ExportDialog
from tests.helper import app  # noqa: F401


def test_ExportDialog_init(mocker):
    _show_starting_instructions_fn = mocker.patch(
        "securedrop_client.gui.conversation.ExportDialog._show_starting_instructions"
    )

    export_dialog = ExportDialog(
        mocker.MagicMock(), "3 files", ["mock.jpg", "memo.txt", "transcript.txt"]
    )

    _show_starting_instructions_fn.assert_called_once_with()
    assert export_dialog.passphrase_form.isHidden()


def test_ExportDialog__show_starting_instructions(mocker, export_dialog_multifile):
    export_dialog_multifile._show_starting_instructions()

    # "3 files" comes from the export_dialog fixture
    assert (
        export_dialog_multifile.header.text() == "Preparing to export:"
        "<br />"
        '<span style="font-weight:normal">3 files</span>'
    )
    assert (
        export_dialog_multifile.body.text()
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
    assert not export_dialog_multifile.header.isHidden()
    assert not export_dialog_multifile.header_line.isHidden()
    assert export_dialog_multifile.error_details.isHidden()
    assert not export_dialog_multifile.body.isHidden()
    assert export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog___show_passphrase_request_message(mocker, export_dialog_multifile):
    export_dialog_multifile._show_passphrase_request_message()

    assert export_dialog_multifile.header.text() == "Enter passphrase for USB drive"
    assert not export_dialog_multifile.header.isHidden()
    assert export_dialog_multifile.header_line.isHidden()
    assert export_dialog_multifile.error_details.isHidden()
    assert export_dialog_multifile.body.isHidden()
    assert not export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__show_passphrase_request_message_again(mocker, export_dialog_multifile):
    export_dialog_multifile._show_passphrase_request_message_again()

    assert export_dialog_multifile.header.text() == "Enter passphrase for USB drive"
    assert (
        export_dialog_multifile.error_details.text()
        == "The passphrase provided did not work. Please try again."
    )
    assert export_dialog_multifile.body.isHidden()
    assert not export_dialog_multifile.header.isHidden()
    assert export_dialog_multifile.header_line.isHidden()
    assert not export_dialog_multifile.error_details.isHidden()
    assert export_dialog_multifile.body.isHidden()
    assert not export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__show_success_message(mocker, export_dialog_multifile):
    export_dialog_multifile._show_success_message()

    assert export_dialog_multifile.header.text() == "Export successful"
    assert (
        export_dialog_multifile.body.text()
        == "Remember to be careful when working with files outside of your Workstation machine."
    )
    assert not export_dialog_multifile.header.isHidden()
    assert not export_dialog_multifile.header_line.isHidden()
    assert export_dialog_multifile.error_details.isHidden()
    assert not export_dialog_multifile.body.isHidden()
    assert export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__show_insert_usb_message(mocker, export_dialog_multifile):
    export_dialog_multifile._show_insert_usb_message()

    assert export_dialog_multifile.header.text() == "Insert encrypted USB drive"
    assert (
        export_dialog_multifile.body.text()
        == "Please insert one of the export drives provisioned specifically "
        "for the SecureDrop Workstation."
    )
    assert not export_dialog_multifile.header.isHidden()
    assert not export_dialog_multifile.header_line.isHidden()
    assert export_dialog_multifile.error_details.isHidden()
    assert not export_dialog_multifile.body.isHidden()
    assert export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__show_insert_encrypted_usb_message(mocker, export_dialog_multifile):
    export_dialog_multifile._show_insert_encrypted_usb_message()

    assert export_dialog_multifile.header.text() == "Insert encrypted USB drive"
    assert (
        export_dialog_multifile.error_details.text()
        == "Either the drive is not encrypted or there is something else wrong with it."
    )
    assert (
        export_dialog_multifile.body.text()
        == "Please insert one of the export drives provisioned specifically for the SecureDrop "
        "Workstation."
    )
    assert not export_dialog_multifile.header.isHidden()
    assert not export_dialog_multifile.header_line.isHidden()
    assert not export_dialog_multifile.error_details.isHidden()
    assert not export_dialog_multifile.body.isHidden()
    assert export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__show_generic_error_message(mocker, export_dialog_multifile):
    export_dialog_multifile.error_status = "mock_error_status"

    export_dialog_multifile._show_generic_error_message()

    assert export_dialog_multifile.header.text() == "Export failed"
    assert (
        export_dialog_multifile.body.text() == "mock_error_status: See your administrator for help."
    )
    assert not export_dialog_multifile.header.isHidden()
    assert not export_dialog_multifile.header_line.isHidden()
    assert export_dialog_multifile.error_details.isHidden()
    assert not export_dialog_multifile.body.isHidden()
    assert export_dialog_multifile.passphrase_form.isHidden()
    assert not export_dialog_multifile.continue_button.isHidden()
    assert not export_dialog_multifile.cancel_button.isHidden()


def test_ExportDialog__export(mocker, export_dialog_multifile):
    device = mocker.MagicMock()
    device.export = mocker.MagicMock()
    export_dialog_multifile._device = device
    export_dialog_multifile.passphrase_field.text = mocker.MagicMock(return_value="mock_passphrase")

    export_dialog_multifile._export()

    device.export.assert_called_once_with(
        export_dialog_multifile.filepaths,
        "mock_passphrase",
    )


def test_ExportDialog__on_export_preflight_check_succeeded(mocker, export_dialog_multifile):
    export_dialog_multifile._show_passphrase_request_message = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    export_dialog_multifile._on_export_preflight_check_succeeded(
        ExportStatus.PRINT_PREFLIGHT_SUCCESS
    )

    export_dialog_multifile._show_passphrase_request_message.assert_not_called()
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_passphrase_request_message
    )


def test_ExportDialog__on_export_preflight_check_succeeded_when_continue_enabled(
    mocker, export_dialog_multifile
):
    export_dialog_multifile._show_passphrase_request_message = mocker.MagicMock()
    export_dialog_multifile.continue_button.setEnabled(True)

    export_dialog_multifile._on_export_preflight_check_succeeded(ExportStatus.DEVICE_LOCKED)

    export_dialog_multifile._show_passphrase_request_message.assert_called_once_with()


def test_ExportDialog__on_export_preflight_check_succeeded_continue_enabled_and_device_unlocked(
    mocker, export_dialog_multifile
):
    export_dialog_multifile._export = mocker.MagicMock()
    export_dialog_multifile.continue_button.setEnabled(True)

    export_dialog_multifile._on_export_preflight_check_succeeded(ExportStatus.DEVICE_WRITABLE)

    export_dialog_multifile._export.assert_called_once_with()


def test_ExportDialog__on_export_preflight_check_succeeded_enabled_after_preflight_success(
    mocker, export_dialog_multifile
):
    assert not export_dialog_multifile.continue_button.isEnabled()
    export_dialog_multifile._on_export_preflight_check_succeeded(ExportStatus.DEVICE_LOCKED)
    assert export_dialog_multifile.continue_button.isEnabled()


def test_ExportDialog__on_export_preflight_check_succeeded_enabled_after_preflight_failure(
    mocker, export_dialog_multifile
):
    assert not export_dialog_multifile.continue_button.isEnabled()
    export_dialog_multifile._on_export_preflight_check_failed(mocker.MagicMock())
    assert export_dialog_multifile.continue_button.isEnabled()


def test_ExportDialog__on_export_preflight_check_failed(mocker, export_dialog_multifile):
    export_dialog_multifile._update_dialog = mocker.MagicMock()

    error = ExportError("mock_error_status")
    export_dialog_multifile._on_export_preflight_check_failed(error)

    export_dialog_multifile._update_dialog.assert_called_with("mock_error_status")


def test_ExportDialog__on_export_succeeded(mocker, export_dialog_multifile):
    export_dialog_multifile._show_success_message = mocker.MagicMock()

    export_dialog_multifile._on_export_succeeded(ExportStatus.SUCCESS_EXPORT)

    export_dialog_multifile._show_success_message.assert_called_once_with()


def test_ExportDialog__on_export_failed(mocker, export_dialog_multifile):
    export_dialog_multifile._update_dialog = mocker.MagicMock()

    error = ExportError("mock_error_status")
    export_dialog_multifile._on_export_failed(error)

    export_dialog_multifile._update_dialog.assert_called_with("mock_error_status")


def test_ExportDialog__update_dialog_when_status_is_USB_NOT_CONNECTED(
    mocker, export_dialog_multifile
):
    export_dialog_multifile._show_insert_usb_message = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog_multifile._update_dialog(ExportStatus.NO_DEVICE_DETECTED)
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_insert_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=True)
    export_dialog_multifile._update_dialog(ExportStatus.NO_DEVICE_DETECTED)
    export_dialog_multifile._show_insert_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_BAD_PASSPHRASE(mocker, export_dialog_multifile):
    export_dialog_multifile._show_passphrase_request_message_again = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog_multifile._update_dialog(ExportStatus.ERROR_UNLOCK_LUKS)
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_passphrase_request_message_again
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=True)
    export_dialog_multifile._update_dialog(ExportStatus.ERROR_UNLOCK_LUKS)  # fka BAD_PASSPHRASE
    export_dialog_multifile._show_passphrase_request_message_again.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_DISK_ENCRYPTION_NOT_SUPPORTED_ERROR(
    mocker, export_dialog_multifile
):
    export_dialog_multifile._show_insert_encrypted_usb_message = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog_multifile._update_dialog(
        ExportStatus.INVALID_DEVICE_DETECTED
    )  # DISK_ENCRYPTION_NOT_SUPPORTED_ERROR
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_insert_encrypted_usb_message
    )

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=True)
    export_dialog_multifile._update_dialog(ExportStatus.INVALID_DEVICE_DETECTED)
    export_dialog_multifile._show_insert_encrypted_usb_message.assert_called_once_with()


def test_ExportDialog__update_dialog_when_status_is_CALLED_PROCESS_ERROR(
    mocker, export_dialog_multifile
):
    export_dialog_multifile._show_generic_error_message = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog_multifile._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_generic_error_message
    )
    assert export_dialog_multifile.error_status == ExportStatus.CALLED_PROCESS_ERROR

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=True)
    export_dialog_multifile._update_dialog(ExportStatus.CALLED_PROCESS_ERROR)
    export_dialog_multifile._show_generic_error_message.assert_called_once_with()
    assert export_dialog_multifile.error_status == ExportStatus.CALLED_PROCESS_ERROR


def test_ExportDialog__update_dialog_when_status_is_unknown(mocker, export_dialog_multifile):
    export_dialog_multifile._show_generic_error_message = mocker.MagicMock()
    export_dialog_multifile.continue_button = mocker.MagicMock()
    export_dialog_multifile.continue_button.clicked = mocker.MagicMock()
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=False)

    # When the continue button is enabled, ensure clicking continue will show next instructions
    export_dialog_multifile._update_dialog("Some Unknown Error Status")
    export_dialog_multifile.continue_button.clicked.connect.assert_called_once_with(
        export_dialog_multifile._show_generic_error_message
    )
    assert export_dialog_multifile.error_status == "Some Unknown Error Status"

    # When the continue button is enabled, ensure next instructions are shown
    mocker.patch.object(export_dialog_multifile.continue_button, "isEnabled", return_value=True)
    export_dialog_multifile._update_dialog("Some Unknown Error Status")
    export_dialog_multifile._show_generic_error_message.assert_called_once_with()
    assert export_dialog_multifile.error_status == "Some Unknown Error Status"
