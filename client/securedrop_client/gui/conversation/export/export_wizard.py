import logging
from gettext import gettext as _
from typing import List

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QIcon, QKeyEvent
from PyQt5.QtWidgets import QApplication, QWizard, QWizardPage

from securedrop_client.export import Export
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.base import SecureQLabel
from securedrop_client.gui.conversation.export.export_wizard_constants import Pages, STATUS_MESSAGES
from securedrop_client.gui.conversation.export.export_wizard_page import (
    ErrorPage,
    FinalPage,
    InsertUSBPage,
    PassphraseWizardPage,
    PreflightPage,
)
from securedrop_client.resources import load_movie

logger = logging.getLogger(__name__)


class ExportWizard(QWizard):
    """
    Guide user through the steps of exporting to a USB.
    """

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260
    BUTTON_CSS = resource_string(__name__, "dialog_button.css").decode("utf-8")

    # If the drive is unlocked, we don't need a passphrase; if we do need one,
    # it's populated later.
    PASS_PLACEHOLDER_FIELD = ""

    def __init__(self, export: Export, summary_text: str, filepaths: List[str]) -> None:
        parent = QApplication.activeWindow()
        super().__init__(parent)
        self.export = export
        self.summary_text = SecureQLabel(
            summary_text, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        self.filepaths = filepaths
        self.current_status = None  # Optional[ExportStatus]

        # Signal from qrexec command runner
        self.export.export_state_changed.connect(self.on_status_received)

        # Clean up export on dialog closed signal
        self.finished.connect(self.export.end_process)

        self._set_layout()
        self._set_pages()
        self._style_buttons()

    def keyPressEvent(self, event: QKeyEvent) -> None:
        if event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return:
            if self.cancel_button.hasFocus():
                self.cancel_button.click()
            else:
                self.next_button.click()
        else:
            super().keyPressEvent(event)

    def text(self) -> str:
        """A text-only representation of the dialog."""
        return self.body.text()

    def _style_buttons(self) -> None:
        self.next_button = self.button(QWizard.WizardButton.NextButton)
        self.next_button.clicked.connect(self.request_export)
        self.next_button.setStyleSheet(self.BUTTON_CSS)
        self.cancel_button = self.button(QWizard.WizardButton.CancelButton)
        self.cancel_button.setStyleSheet(self.BUTTON_CSS)

        # Activestate animation
        self.button_animation = load_movie("activestate-wide.gif")
        self.button_animation.setScaledSize(QSize(32, 32))
        self.button_animation.frameChanged.connect(self.animate_activestate)

    def animate_activestate(self) -> None:
        self.next_button.setIcon(QIcon(self.button_animation.currentPixmap()))

    def start_animate_activestate(self) -> None:
        self.button_animation.start()
        self.next_button.setMinimumSize(QSize(142, 43))
        # Reset widget stylesheets
        self.next_button.setStyleSheet("")
        self.next_button.setObjectName("ModalDialog_primary_button_active")
        self.next_button.setStyleSheet(self.BUTTON_CSS)

    def stop_animate_activestate(self) -> None:
        self.next_button.setIcon(QIcon())
        self.button_animation.stop()
        # Reset widget stylesheets
        self.next_button.setStyleSheet("")
        self.next_button.setObjectName("ModalDialog_primary_button")
        self.next_button.setStyleSheet(self.BUTTON_CSS)

    def _set_layout(self) -> None:
        self.setWindowTitle(f"Export {self.summary_text}")
        self.setModal(False)
        self.setOptions(
            QWizard.NoBackButtonOnLastPage
            | QWizard.NoCancelButtonOnLastPage
            | QWizard.NoBackButtonOnStartPage
        )

    def _set_pages(self) -> None:
        for page in [
            self._create_preflight(),
            self._create_errorpage(),
            self._create_insert_usb(),
            self._create_passphrase_prompt(),
            self._create_done(),
        ]:
            self.addPage(page)

            # Nice to have, but steals the focus from the password field after 1 character is typed.
            # Probably another way to have it be based on validating the status
            # page.completeChanged.connect(lambda: self._set_focus(QWizard.WizardButton.NextButton))

    @pyqtSlot(int)
    def _set_focus(self, which: QWizard.WizardButton) -> None:
        self.button(which).setFocus()

    def request_export(self) -> None:
        logger.debug("Request export")
        # Registered fields let us access the passphrase field
        # of the PassphraseRequestPage from the wizard parent
        passphrase_untrusted = self.field("passphrase")
        if str(passphrase_untrusted) is not None:
            self.export.export(self.filepaths, str(passphrase_untrusted))
        else:
            self.export.export(self.filepaths, self.PASS_PLACEHOLDER_FIELD)

    def request_export_preflight(self) -> None:
        logger.debug("Request preflight check")
        self.export.run_export_preflight_checks()

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        """
        Update the wizard position based on incoming ExportStatus.
        If a status is shown that represents a removed device,
        rewind the wizard to the appropriate pane.

        To update the text on an individual page, the page listens
        for this signal and can call `update_content` in the listener.
        """
        logger.debug(f"Wizard received {status.value}")

        # Unrecoverable - end the wizard
        if status in [
            ExportStatus.ERROR_MOUNT,
            ExportStatus.ERROR_EXPORT,
            ExportStatus.ERROR_MISSING_FILES,
            ExportStatus.DEVICE_ERROR,
            ExportStatus.CALLED_PROCESS_ERROR,
            ExportStatus.UNEXPECTED_RETURN_STATUS,
        ]:
            logger.error(f"Encountered {status.value}, cannot export")
            self.end_wizard_with_error(status)
            return

        target = None  # Optional[PageEnum]
        if status in [
            ExportStatus.NO_DEVICE_DETECTED,
            ExportStatus.MULTI_DEVICE_DETECTED,
            ExportStatus.INVALID_DEVICE_DETECTED,
        ]:
            target = Pages.INSERT_USB
        elif status in [ExportStatus.DEVICE_LOCKED, ExportStatus.ERROR_UNLOCK_LUKS]:
            target = Pages.UNLOCK_USB

        # Someone may have yanked out or unmounted a USB
        if target:
            self.rewind(target)

        # If the user is stuck, show them a hint.
        should_show_hint = target == self.currentId()
        logger.debug(f"{status.value} - should show hint is {should_show_hint}")

        page = self.currentPage()
        # Sometimes self.currentPage() is None
        if page and should_show_hint:
            page.update_content(status, should_show_hint)

        # Update status
        self.current_status = status

    def rewind(self, target: Pages) -> None:
        """
        Navigate back to target page.
        """
        while self.currentId() > target:
            self.back()

    def end_wizard_with_error(self, error: ExportStatus) -> None:
        """
        If and end state is reached, display message and let user
        end the wizard.
        """
        if isinstance(self.currentPage(), PreflightPage):
            # Update its status so it shows error next self.currentPage()
            # self.next()
            logger.debug("On preflight page")
        else:
            while self.currentId() > Pages.ERROR:
                self.back()
        page = self.currentPage()
        page.update_content(error)

    def _create_preflight(self) -> QWizardPage:
        return PreflightPage(self.export, self.summary_text)

    def _create_errorpage(self) -> QWizardPage:
        return ErrorPage(self.export, "")

    def _create_insert_usb(self) -> QWizardPage:
        return InsertUSBPage(self.export, self.summary_text)

    def _create_passphrase_prompt(self) -> QWizardPage:
        return PassphraseWizardPage(self.export)

    # def _create_export(self) -> QWizardPage:
    #     return ExportPage(self.export)

    # readywhen: all done
    def _create_done(self) -> QWizardPage:
        return FinalPage(self.export)
