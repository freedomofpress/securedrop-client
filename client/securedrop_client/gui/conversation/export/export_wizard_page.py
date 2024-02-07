import logging
from gettext import gettext as _
from typing import Optional

from pkg_resources import resource_string
from PyQt5.QtCore import QSize, Qt, pyqtSlot
from PyQt5.QtGui import QColor, QFont, QPixmap
from PyQt5.QtWidgets import (
    QApplication,
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

    def __init__(self, export: Export, header: str, body: Optional[str]) -> None:
        parent = QApplication.activeWindow()
        super().__init__(parent)
        self.export = export
        self.header_text = header
        self.body_text = body
        self.status = None  # Optional[ExportStatus]
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
        self.setStyleSheet(self.WIZARD_CSS)
        parent_layout = QVBoxLayout(self)
        parent_layout.setContentsMargins(self.MARGIN, self.MARGIN, self.MARGIN, self.MARGIN)

        # Header for icon and task title
        header_container = QWidget()
        header_container_layout = QHBoxLayout()
        header_container.setLayout(header_container_layout)
        self.header_icon = SvgLabel("blank.svg", svg_size=QSize(64, 64))
        self.header_icon.setObjectName("QWizard_header_icon")
        self.header_spinner = QPixmap()
        self.header_spinner_label = QLabel()
        self.header_spinner_label.setObjectName("QWizard_header_spinner")
        self.header_spinner_label.setMinimumSize(64, 64)
        self.header_spinner_label.setVisible(False)
        self.header_spinner_label.setPixmap(self.header_spinner)
        self.header = QLabel()
        self.header.setObjectName("QWizard_header")
        header_container_layout.addWidget(self.header, alignment=Qt.AlignCenter)
        header_container_layout.addWidget(self.header_icon)
        header_container_layout.addWidget(self.header_spinner_label)
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

    def update_content(self, status: ExportStatus, should_show_hint: bool = False) -> None:
        """
        Update page's content based on new status.
        Children may re-implement this method.
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
        self.export.run_export_preflight_checks()

    def nextId(self) -> int:
        """
        Override builtin to allow bypassing the password page if device is unlocked.
        """
        if self.status == ExportStatus.DEVICE_WRITABLE:
            logger.debug("Skip password prompt")
            return Pages.EXPORT_DONE
        elif self.status == ExportStatus.DEVICE_LOCKED:
            logger.debug("Device locked - prompt for passphrase")
            return Pages.UNLOCK_USB
        elif self.status in (
            ExportStatus.CALLED_PROCESS_ERROR,
            ExportStatus.DEVICE_ERROR,
            ExportStatus.UNEXPECTED_RETURN_STATUS,
        ):
            logger.debug("Error during preflight - show error page")
            return Pages.ERROR
        else:
            return Pages.INSERT_USB

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        self.stop_animate_header()
        header = _("Ready to export:<br />" '<span style="font-weight:normal">{}</span>').format(
            self.summary
        )
        self.header.setText(header)
        self.status = status


class ErrorPage(ExportWizardPage):
    def __init__(self, export: Export):
        header = _("Export Failed")
        super().__init__(export, header=header, body=None)

    def isComplete(self) -> bool:
        return False

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        pass


class InsertUSBPage(ExportWizardPage):
    def __init__(self, export: Export, summary: str) -> None:
        self.summary = summary
        header = _("Ready to export:<br />" '<span style="font-weight:normal">{}</span>').format(
            summary
        )
        body = _(
            "Please insert one of the export drives provisioned specifically "
            "for the SecureDrop Workstation."
        )
        super().__init__(export, header=header, body=body)

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        logger.debug(f"InsertUSB received {status.value}")
        should_show_hint = status in (
            ExportStatus.MULTI_DEVICE_DETECTED,
            ExportStatus.INVALID_DEVICE_DETECTED,
        ) or (
            self.status == status == ExportStatus.NO_DEVICE_DETECTED
            and isinstance(self.wizard().currentPage, InsertUSBPage)
        )
        self.update_content(status, should_show_hint)
        self.status = status
        self.completeChanged.emit()
        if status in (ExportStatus.DEVICE_LOCKED, ExportStatus.DEVICE_WRITABLE) and isinstance(
            self.wizard().currentPage(), InsertUSBPage
        ):
            logger.debug("Device detected - advance the wizard")
            self.wizard().next()

    def validatePage(self) -> bool:
        """
        Override method to implement custom validation logic, which
        shows an error-specific hint to the user.
        """
        if self.status in (ExportStatus.DEVICE_WRITABLE, ExportStatus.DEVICE_LOCKED):
            self.error_details.hide()
            return True
        else:
            logger.debug(f"Status is {self.status}")

            # Show the user a hint
            if self.status in (
                ExportStatus.MULTI_DEVICE_DETECTED,
                ExportStatus.NO_DEVICE_DETECTED,
                ExportStatus.INVALID_DEVICE_DETECTED,
            ):
                self.update_content(self.status, should_show_hint=True)
                return False
            else:
                # Status may be None here
                logger.warning("InsertUSBPage encountered unexpected status")
                return super().validatePage()

    def nextId(self) -> int:
        """
        Override builtin to allow bypassing the password page if device unlocked
        """
        if self.status == ExportStatus.DEVICE_WRITABLE:
            logger.debug("Skip password prompt")
            return Pages.EXPORT_DONE
        elif self.status == ExportStatus.DEVICE_LOCKED:
            return Pages.UNLOCK_USB
        elif self.status in (ExportStatus.UNEXPECTED_RETURN_STATUS, ExportStatus.DEVICE_ERROR):
            return Pages.ERROR
        else:
            next = super().nextId()
            value = self.status.value if self.status else "(no status supplied)"
            logger.debug(f"Unexpected status on InsertUSBPage: {value}. nextID is {next}")
            return next


class FinalPage(ExportWizardPage):
    def __init__(self, export: Export) -> None:
        header = _("Export successful")
        body = _(
            "Remember to be careful when working with files outside of your Workstation machine."
        )
        super().__init__(export, header, body)

    @pyqtSlot(object)
    def on_status_received(self, status: ExportStatus) -> None:
        logger.debug(f"Final page received status {status}")
        self.update_content(status)
        self.status = status

    def update_content(self, status: ExportStatus, should_show_hint: bool = False) -> None:
        header = None
        body = None
        if status == ExportStatus.SUCCESS_EXPORT:
            header = _("Export successful")
            body = _(
                "Remember to be careful when working with files "
                "outside of your Workstation machine."
            )
        elif status == ExportStatus.ERROR_EXPORT_CLEANUP:
            header = header = _("Export sucessful, but drive was not locked")
            body = STATUS_MESSAGES.get(ExportStatus.ERROR_EXPORT_CLEANUP)

        else:
            header = _("Working...")

        self.header.setText(header)
        if body:
            self.body.setText(body)


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
        logger.debug(f"Passphrase page rececived {status.value}")
        should_show_hint = status in (
            ExportStatus.ERROR_UNLOCK_LUKS,
            ExportStatus.ERROR_UNLOCK_GENERIC,
        )
        self.update_content(status, should_show_hint)
        self.status = status
        self.completeChanged.emit()
        if status in (
            ExportStatus.SUCCESS_EXPORT,
            ExportStatus.ERROR_EXPORT_CLEANUP,
        ) and isinstance(self.wizard().currentPage(), PassphraseWizardPage):
            self.wizard().next()

    def validatePage(self) -> bool:
        # Also to add: DEVICE_BUSY for unmounting.
        # This shouldn't stop us from going "back" to an error page
        return self.status in (
            ExportStatus.DEVICE_WRITABLE,
            ExportStatus.SUCCESS_EXPORT,
            ExportStatus.ERROR_EXPORT_CLEANUP,
        )

    def nextId(self) -> int:
        if self.status == ExportStatus.SUCCESS_EXPORT:
            return Pages.EXPORT_DONE
        elif self.status in (ExportStatus.ERROR_UNLOCK_LUKS, ExportStatus.ERROR_UNLOCK_GENERIC):
            return Pages.UNLOCK_USB
        elif self.status in (
            ExportStatus.NO_DEVICE_DETECTED,
            ExportStatus.MULTI_DEVICE_DETECTED,
            ExportStatus.INVALID_DEVICE_DETECTED,
        ):
            return Pages.INSERT_USB
        elif self.status in (
            ExportStatus.ERROR_MOUNT,
            ExportStatus.ERROR_EXPORT,
            ExportStatus.ERROR_EXPORT_CLEANUP,
            ExportStatus.UNEXPECTED_RETURN_STATUS,
        ):
            return Pages.ERROR
        else:
            return super().nextId()
