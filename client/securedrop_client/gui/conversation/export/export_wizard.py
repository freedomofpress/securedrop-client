import logging
from gettext import gettext as _
from typing import Optional

from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QIcon, QKeyEvent
from PyQt5.QtWidgets import (
    QAbstractButton,
    QApplication,
    QWidget,
    QWizard,
    QWizardPage,
)

from securedrop_client.export import Export
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.base import SecureQLabel
from securedrop_client.gui.conversation.export.export_wizard_constants import Pages
from securedrop_client.gui.conversation.export.export_wizard_page import (
    ErrorPage,
    ExportWizardPage,
    FinalPage,
    InsertUSBPage,
    PassphraseWizardPage,
    PreflightPage,
)
from securedrop_client.resources import load_movie, load_relative_css

logger = logging.getLogger(__name__)


class ExportWizard(QWizard):
    """
    Guide user through the steps of exporting to a USB.
    """

    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260
    FILE_OPTIONS_FONT_SPACING = 1.6

    # If the drive is unlocked, we don't need a passphrase; if we do need one,
    # it's populated later.
    PASS_PLACEHOLDER_FIELD = ""

    def __init__(
        self,
        export: Export,
        summary_text: str,
        filepaths: list[str],
        parent: Optional[QWidget] = None,
    ) -> None:
        # Normally, the active window is the right parent, but if the wizard is launched
        # via another element (a modal dialog, such as the "Some files may not be exported"
        # modal), the parent will be the modal dialog and the wizard layout will be affected.
        # In those cases we want to be able to specify a different parent.
        if not parent:
            parent = QApplication.activeWindow()
        super().__init__(parent)
        self.export = export
        self.summary_text = SecureQLabel(
            summary_text, wordwrap=False, max_length=self.FILENAME_WIDTH_PX
        ).text()
        self.filepaths = filepaths
        self.current_status: Optional[ExportStatus] = None

        # Signal from qrexec command runner
        self.export.export_state_changed.connect(self.on_status_received)

        # Sends cleanup signal to export if wizard is closed or completed.
        # (Avoid orphaned QProcess)
        self.finished.connect(self.export.end_process)

        self._style_buttons()
        self._set_layout()
        self._set_pages()
        self.adjustSize()

    def keyPressEvent(self, event: QKeyEvent) -> None:
        """
        Allow for keyboard navigation of wizard buttons.
        """
        if event.key() == Qt.Key_Enter or event.key() == Qt.Key_Return:
            if self.cancel_button.hasFocus():
                self.cancel_button.click()
            elif self.back_button.hasFocus():
                self.back_button.click()
            else:
                self.next_button.click()
        else:
            super().keyPressEvent(event)

    def _style_buttons(self) -> None:
        """
        Style QWizard buttons and connect "Next" button click event to
        request_export slot.
        """
        # Activestate animation
        self.button_animation = load_movie("activestate-wide.gif")
        self.button_animation.setScaledSize(QSize(32, 32))
        self.button_animation.frameChanged.connect(self._animate_activestate)
        button_stylesheet = load_relative_css(__file__, "wizard_button.css")

        # Buttons
        self.next_button: QAbstractButton = self.button(QWizard.WizardButton.NextButton)
        self.cancel_button: QAbstractButton = self.button(QWizard.WizardButton.CancelButton)
        self.back_button: QAbstractButton = self.button(QWizard.WizardButton.BackButton)
        self.finish_button: QAbstractButton = self.button(QWizard.WizardButton.FinishButton)

        self.next_button.setObjectName("QWizardButton_PrimaryButton")
        self.next_button.setStyleSheet(button_stylesheet)
        self.next_button.setMinimumSize(QSize(142, 40))
        self.next_button.setMaximumHeight(40)
        self.next_button.setIconSize(QSize(21, 21))
        self.next_button.clicked.connect(self.request_export)
        self.next_button.setFixedSize(QSize(142, 40))

        self.cancel_button.setObjectName("QWizardButton_GenericButton")
        self.cancel_button.setStyleSheet(button_stylesheet)
        self.cancel_button.setMinimumSize(QSize(142, 40))
        self.cancel_button.setMaximumHeight(40)
        self.cancel_button.setFixedSize(QSize(142, 40))

        self.back_button.setObjectName("QWizardButton_GenericButton")
        self.back_button.setStyleSheet(button_stylesheet)
        self.back_button.setMinimumSize(QSize(142, 40))
        self.back_button.setMaximumHeight(40)
        self.back_button.setFixedSize(QSize(142, 40))

        self.finish_button.setObjectName("QWizardButton_GenericButton")
        self.finish_button.setStyleSheet(button_stylesheet)
        self.finish_button.setMinimumSize(QSize(142, 40))
        self.finish_button.setMaximumHeight(40)
        self.finish_button.setFixedSize(QSize(142, 40))

        self.setButtonText(QWizard.WizardButton.NextButton, _("CONTINUE"))
        self.setButtonText(QWizard.WizardButton.CancelButton, _("CANCEL"))
        self.setButtonText(QWizard.WizardButton.FinishButton, _("DONE"))
        self.setButtonText(QWizard.WizardButton.BackButton, _("BACK"))

    def _animate_activestate(self) -> None:
        self.next_button.setIcon(QIcon(self.button_animation.currentPixmap()))

    def _start_animate_activestate(self) -> None:
        self.button_animation.start()

    def _stop_animate_activestate(self) -> None:
        self.next_button.setIcon(QIcon())
        self.button_animation.stop()

    def _set_layout(self) -> None:
        title = f"Export {self.summary_text}"
        self.setWindowTitle(title)
        self.setObjectName("QWizard_export")
        self.setStyleSheet(load_relative_css(__file__, "wizard.css"))
        self.setModal(False)
        self.setOptions(
            QWizard.NoBackButtonOnLastPage
            | QWizard.NoCancelButtonOnLastPage
            | QWizard.NoBackButtonOnStartPage
        )

    def _set_pages(self) -> None:
        for id, page in [
            (Pages.PREFLIGHT, self._create_preflight()),
            (Pages.ERROR, self._create_errorpage()),
            (Pages.INSERT_USB, self._create_insert_usb()),
            (Pages.UNLOCK_USB, self._create_passphrase_prompt()),
            (Pages.EXPORT_DONE, self._create_done()),
        ]:
            self.setPage(id, page)
            self.adjustSize()

    @pyqtSlot()
    def request_export(self) -> None:
        """
        Handler for "next" button clicks. Start animation and request export.
        (The export proceeds only as far as it's able, which is why it's
        possible to trigger the same method on every dialog page).

        The Preflight QWizardPage triggers the preflight check itself when
        it is created, so there is no corresponding `request_export_preflight`
        method.
        """
        logger.debug("Request export")
        # While we're waiting for the results to come back, stay on the same page.
        # This prevents the dialog from briefly flashing one page and then
        # advancing to a subsequent page (for example, flashing the "Insert a USB"
        # page before detecting the USB and advancing to the "Unlock USB" page)
        page = self.currentPage()
        if isinstance(page, ExportWizardPage):
            page.set_complete(False)
        self._start_animate_activestate()

        # Registered fields let us access the passphrase field
        # of the PassphraseRequestPage from the wizard parent
        passphrase_untrusted = self.field("passphrase")
        if str(passphrase_untrusted) is not None:
            self.export.export(self.filepaths, str(passphrase_untrusted))
        else:
            self.export.export(self.filepaths, self.PASS_PLACEHOLDER_FIELD)

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        """
        Receive status update from export process in order to update the animation.
        Child QWizardPages also implement this listener in order to update their own UI and store
        a reference to the current status.

        Adjusting the QWizard control flow based on ExportStatus is handled by each child page.
        """
        # Release the page (page was held during "next" button click event)
        page = self.currentPage()
        if isinstance(page, ExportWizardPage):
            page.set_complete(True)
        self._stop_animate_activestate()
        self.current_status = status

    def _create_preflight(self) -> QWizardPage:
        return PreflightPage(self.export, self.summary_text)

    def _create_errorpage(self) -> QWizardPage:
        return ErrorPage(self.export)

    def _create_insert_usb(self) -> QWizardPage:
        return InsertUSBPage(self.export, self.summary_text)

    def _create_passphrase_prompt(self) -> QWizardPage:
        return PassphraseWizardPage(self.export)

    def _create_done(self) -> QWizardPage:
        return FinalPage(self.export)
