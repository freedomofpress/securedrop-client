import logging
from gettext import gettext as _
from typing import Optional

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QColor, QFont, QPixmap
from PyQt5.QtWidgets import (
    QGraphicsDropShadowEffect,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QVBoxLayout,
    QWidget,
    QWizardPage,
)

from securedrop_client.export import Export
from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.base import PasswordEdit, SecureQLabel
from securedrop_client.gui.base.checkbox import SDCheckBox
from securedrop_client.gui.base.misc import SvgLabel
from securedrop_client.gui.conversation.export.export_wizard_constants import STATUS_MESSAGES, Pages
from securedrop_client.resources import load_movie

logger = logging.getLogger(__name__)


class ExportWizardPage(QWizardPage):
    """
    Base class for all export wizard pages. Individual pages must inherit
    from this class to:
        * Implement `on_status_received`, a listener that receives export
          statuses in order to update the UI and store a reference to the
          current state.
        * Include additional layout items
        * Implement dynamic ordering (i.e., if the next window varies
          depending on the result of the previous action, in which case the
          `nextId()` method must be overwritten)
        * Implement custom validation (logic that prevents a user
          from skipping to the next page until conditions are met)

    Every wizard page has:
        * A header (page title)
        * Body (instructions)
        * Optional error_instructions (Additional text that is hidden but
          appears on recoverable error to help the user advance to the next stage)
    """

    WIZARD_CSS = resource_string(__name__, "wizard.css").decode("utf-8")
    ERROR_DETAILS_CSS = resource_string(__name__, "wizard_message.css").decode("utf-8")

    MARGIN = 40
    PASSPHRASE_LABEL_SPACING = 0.5
    NO_MARGIN = 0
    FILENAME_WIDTH_PX = 260

    # All pages should show the error page if these errors are encountered
    UNRECOVERABLE_ERRORS = [
        ExportStatus.ERROR_MOUNT,
        ExportStatus.ERROR_EXPORT,
        ExportStatus.ERROR_MISSING_FILES,
        ExportStatus.DEVICE_ERROR,
        ExportStatus.CALLED_PROCESS_ERROR,
        ExportStatus.UNEXPECTED_RETURN_STATUS,
    ]

    def __init__(self, export: Export, header: str, body: Optional[str]) -> None:
        super().__init__()
        self.export = export
        self.header_text = header
        self.body_text = body
        self.status: Optional[ExportStatus] = None
        self._is_complete = True  # Won't override parent method unless explicitly set to False

        self.setLayout(self._build_layout())

        # Listen for export updates from export.
        # Pages will receive signals even if they are not the current active page.
        self.export.export_state_changed.connect(self.on_status_received)

    def set_complete(self, is_complete: bool) -> None:
        """
        Flag a page as being incomplete. (Disables Next button and prevents
        user from advancing to next page)
        """
        self._is_complete = is_complete

    def isComplete(self) -> bool:
        return self._is_complete and super().isComplete()

    def _build_layout(self) -> QVBoxLayout:
        """
        Create parent layout, draw elements, return parent layout
        """
        self.setObjectName("QWizard_export_page")
        self.setStyleSheet(self.WIZARD_CSS)
        parent_layout = QVBoxLayout(self)
        parent_layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)

        # Header for icon and task title
        header_container = QWidget()
        header_container_layout = QHBoxLayout()
        header_container.setLayout(header_container_layout)
        header_container.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        self.header_icon = SvgLabel("savetodisk.svg", svg_size=QSize(64, 64))
        self.header_icon.setObjectName("QWizard_header_icon")
        self.header_spinner = QPixmap()
        self.header_spinner_label = QLabel()
        self.header_spinner_label.setObjectName("QWizard_header_spinner")
        self.header_spinner_label.setMinimumSize(64, 64)
        self.header_spinner_label.setVisible(False)
        self.header_spinner_label.setPixmap(self.header_spinner)
        self.header = QLabel()
        self.header.setObjectName("QWizard_header")
        header_container_layout.addWidget(self.header_icon)
        header_container_layout.addWidget(self.header_spinner_label)
        header_container_layout.addWidget(self.header, alignment=Qt.AlignCenter)
        header_container_layout.addStretch()
        self.header_line = QWidget()
        self.header_line.setObjectName("QWizard_header_line")

        # Body to display instructions and forms
        self.body = QLabel()
        self.body.setObjectName("QWizard_body")
        self.body.setWordWrap(True)
        self.body.setScaledContents(True)

        body_container = QWidget()
        self.body_layout = QVBoxLayout()
        self.body_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        body_container.setLayout(self.body_layout)
        self.body_layout.addWidget(self.body)

        # Widget for displaying error messages (hidden by default)
        self.error_details = QLabel()
        self.error_details.setObjectName("QWizard_error_details")
        self.error_details.setStyleSheet(self.ERROR_DETAILS_CSS)
        self.error_details.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        self.error_details.setWordWrap(True)
        self.error_details.hide()

        # Header animation
        self.header_animation = load_movie("header_animation.gif")
        self.header_animation.setScaledSize(QSize(64, 64))
        self.header_animation.frameChanged.connect(self.animate_header)

        # Populate text content
        self.header.setText(self.header_text)
        if self.body_text:
            self.body.setText(self.body_text)

        # Add all the layout elements
        parent_layout.addWidget(header_container)
        parent_layout.addWidget(self.header_line)
        parent_layout.addWidget(body_container)
        parent_layout.addWidget(self.error_details)
        parent_layout.addStretch()

        return parent_layout

    def animate_header(self) -> None:
        self.header_spinner_label.setPixmap(self.header_animation.currentPixmap())

    def start_animate_header(self) -> None:
        self.header_icon.setVisible(False)
        self.header_spinner_label.setVisible(True)
        self.header_animation.start()

    def stop_animate_header(self) -> None:
        self.header_icon.setVisible(True)
        self.header_spinner_label.setVisible(False)
        self.header_animation.stop()

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        raise NotImplementedError("Children must implement")

    def nextId(self) -> int:
        """
        Override builtin QWizardPage nextId() method to create custom control flow.
        """
        if self.status is not None:
            if self.status in (
                ExportStatus.DEVICE_WRITABLE,
                ExportStatus.SUCCESS_EXPORT,
                ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY,
                ExportStatus.ERROR_EXPORT_CLEANUP,
            ):
                return Pages.EXPORT_DONE
            elif self.status in (
                ExportStatus.DEVICE_LOCKED,
                ExportStatus.ERROR_UNLOCK_LUKS,
                ExportStatus.ERROR_UNLOCK_GENERIC,
            ):
                return Pages.UNLOCK_USB
            elif self.status in (
                ExportStatus.NO_DEVICE_DETECTED,
                ExportStatus.MULTI_DEVICE_DETECTED,
                ExportStatus.INVALID_DEVICE_DETECTED,
            ):
                return Pages.INSERT_USB
            elif self.status in self.UNRECOVERABLE_ERRORS:
                return Pages.ERROR

        return super().nextId()

    def update_content(self, status: ExportStatus, should_show_hint: bool = False) -> None:
        """
        Update page's content based on new status.
        """
        if not status:
            logger.error("Empty status value given to update_content")
            status = ExportStatus.UNEXPECTED_RETURN_STATUS

        if should_show_hint:
            message = STATUS_MESSAGES.get(status)
            if message:
                self.error_details.setText(message)
                self.error_details.show()
        else:
            self.error_details.hide()


class PreflightPage(ExportWizardPage):
    def __init__(self, export: Export, summary: str) -> None:
        self._should_autoskip_preflight = False
        self.summary = summary
        header = _(
            "Preparing to export:<br />" '<span style="font-weight:normal">{}</span>'
        ).format(summary)
        body = _(
            "<h2>Understand the risks before exporting files</h2>"
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

        super().__init__(export, header=header, body=body)
        self.start_animate_header()

        # Don't need preflight check every time, just when the wizard is initialized
        if self.status is None:
            self.set_complete(False)
            self.completeChanged.emit()
            self.export.run_export_preflight_checks()

    def set_should_autoskip_preflight(self, should_autoskip: bool) -> None:
        """
        Provide setter for auto-advancing wizard past the Preflight page.
        If True, as soon as a Status is available, the wizard will advance
        to the appropriate page.
        """
        self._should_autoskip_preflight = should_autoskip

    def should_autoskip_preflight(self) -> bool:
        """
        Return True if Preflight page should be advanced automatically as soon as
        a given status is available.

        This workaround exists to let users skip past the preflight page if they are
        returned to it from a later page. This is required because in PyQt5,
        QWizard cannot navigate to a specific page, meaning users who insert an
        unlocked drive, then start the wizard, then encounter a problem are sent
        "back" to this page rather than to the InsertUSBPage, since it wasn't in
        their call stack.

        The autoskip combined with custom nextId logic in ExporWizardPage allows us
        to emulate the desired behaviour.
        """
        return self._should_autoskip_preflight

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.status = status
        self.stop_animate_header()
        header = _("Ready to export:<br />" '<span style="font-weight:normal">{}</span>').format(
            self.summary
        )
        self.header.setText(header)
        self.set_complete(True)
        self.completeChanged.emit()

        if self.wizard() and isinstance(self.wizard().currentPage(), PreflightPage):
            # Let users skip preflight screen if they have already seen it. The first time a status
            # is received, autoskip is False, and a user has to manually click "Continue";
            # after that, it's True.
            if self.should_autoskip_preflight():
                self.wizard().next()
            else:
                self.set_should_autoskip_preflight(True)


class ErrorPage(ExportWizardPage):
    def __init__(self, export: Export):
        header = _("Export Failed")
        super().__init__(export, header=header, body=None)

    def isComplete(self) -> bool:
        """
        Override isComplete() to always return False. This disables
        the 'next' button on the error page and means users can
        only go back to a previous page or exit the wizard.
        """
        return False

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.status = status


class InsertUSBPage(ExportWizardPage):
    def __init__(self, export: Export, summary: str) -> None:
        self.no_device_hint = 0
        self.summary = summary
        header = _("Ready to export:<br />" '<span style="font-weight:normal">{}</span>').format(
            summary
        )
        body = _(
            "Please insert one of the export drives provisioned specifically "
            "for the SecureDrop Workstation."
            "<br />"
            "If you're using a VeraCrypt drive, unlock it manually before proceeding."
        )
        super().__init__(export, header=header, body=body)

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.status = status
        if self.wizard() and isinstance(self.wizard().currentPage(), InsertUSBPage):
            logger.debug(f"InsertUSB received {status.value}")
            if status in (
                ExportStatus.MULTI_DEVICE_DETECTED,
                ExportStatus.INVALID_DEVICE_DETECTED,
                ExportStatus.DEVICE_WRITABLE,
            ):
                self.update_content(status, should_show_hint=True)
            elif status == ExportStatus.NO_DEVICE_DETECTED:
                if self.no_device_hint > 0:
                    self.update_content(status, should_show_hint=True)
                self.no_device_hint += 1
            else:
                # Hide the error hint, it visible, so that if the user navigates
                # forward then back they don't see an unneeded hint
                self.error_details.hide()
                self.wizard().next()

    def validatePage(self) -> bool:
        """
        Implement custom validation logic.
        """
        if self.status is not None:
            return self.status not in (
                ExportStatus.NO_DEVICE_DETECTED,
                ExportStatus.INVALID_DEVICE_DETECTED,
                ExportStatus.MULTI_DEVICE_DETECTED,
            )
        else:
            return super().isComplete()


class FinalPage(ExportWizardPage):
    def __init__(self, export: Export) -> None:
        header = _("Export successful")
        body = _(
            "Remember to be careful when working with files outside of your Workstation machine."
        )
        super().__init__(export, header, body)

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.status = status
        self.update_content(status)

        # The completeChanged signal alerts the page to recheck its completion status,
        # which we need to signal since we have custom isComplete() logic
        if self.wizard() and isinstance(self.wizard().currentPage(), FinalPage):
            self.completeChanged.emit()

    def update_content(self, status: ExportStatus, should_show_hint: bool = False) -> None:
        header = None
        body = None
        if status == ExportStatus.SUCCESS_EXPORT:
            header = _("Export successful")
            body = _(
                "Remember to be careful when working with files "
                "outside of your Workstation machine."
            )
        elif status in (ExportStatus.ERROR_EXPORT_CLEANUP, ExportStatus.ERROR_UNMOUNT_VOLUME_BUSY):
            header = _("Export sucessful, but drive was not locked")
            body = STATUS_MESSAGES.get(status)

        else:
            header = _("Working...")

        self.header.setText(header)
        if body:
            self.body.setText(body)

    def isComplete(self) -> bool:
        """
        Override the default isComplete() implementation in order to disable the "Finish"
        button while an export is taking place. (If the "Working...." header is being shown,
        the export is still in progress and "Finish" should not be clickable.)
        """
        if self.status:
            return self.status not in (
                ExportStatus.DEVICE_WRITABLE,
                ExportStatus.DEVICE_LOCKED,
            )
        else:
            return True

    def nextId(self) -> int:
        """
        The final page should not have any custom nextId() logic.
        Disable it to ensure the Finished button ("Done") is shown.
        """
        return -1


class PassphraseWizardPage(ExportWizardPage):
    """
    Wizard page that includes a passphrase prompt field
    """

    def __init__(self, export: Export) -> None:
        header = _("Enter passphrase for USB drive")
        super().__init__(export, header, body=None)

    def _build_layout(self) -> QVBoxLayout:
        layout = super()._build_layout()

        # Passphrase Form
        self.passphrase_form = QWidget()
        self.passphrase_form.setObjectName("QWizard_passphrase_form")
        passphrase_form_layout = QVBoxLayout()
        passphrase_form_layout.setContentsMargins(
            self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN, self.NO_MARGIN
        )
        self.passphrase_form.setLayout(passphrase_form_layout)
        passphrase_label = SecureQLabel(_("Passphrase"))
        font = QFont()
        font.setLetterSpacing(QFont.AbsoluteSpacing, self.PASSPHRASE_LABEL_SPACING)
        passphrase_label.setFont(font)
        self.passphrase_field = PasswordEdit(self)
        self.passphrase_form.setObjectName("QWizard_passphrase_form")
        self.passphrase_field.setEchoMode(QLineEdit.Password)
        effect = QGraphicsDropShadowEffect(self)
        effect.setOffset(0, -1)
        effect.setBlurRadius(4)
        effect.setColor(QColor("#aaa"))
        self.passphrase_field.setGraphicsEffect(effect)

        # Makes the password text accessible outside of this panel
        self.registerField("passphrase*", self.passphrase_field)

        check = SDCheckBox()
        check.checkbox.stateChanged.connect(self.passphrase_field.on_toggle_password_Action)

        passphrase_form_layout.addWidget(passphrase_label)
        passphrase_form_layout.addWidget(self.passphrase_field)
        passphrase_form_layout.addWidget(check, alignment=Qt.AlignRight)

        layout.insertWidget(1, self.passphrase_form)
        return layout

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.status = status
        if self.wizard() and isinstance(self.wizard().currentPage(), PassphraseWizardPage):
            logger.debug(f"Passphrase page received {status.value}")
            if status in (
                ExportStatus.ERROR_UNLOCK_LUKS,
                ExportStatus.ERROR_UNLOCK_GENERIC,
            ):
                self.update_content(status, should_show_hint=True)
            else:
                self.wizard().next()

    def validatePage(self) -> bool:
        return self.status not in (
            ExportStatus.ERROR_UNLOCK_LUKS,
            ExportStatus.ERROR_UNLOCK_GENERIC,
            ExportStatus.DEVICE_LOCKED,
        )
