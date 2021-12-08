"""
A conversation widget representing a file.

Copyright (C) 2021  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""
import logging
from gettext import gettext as _

from PyQt5.QtCore import QEvent, QObject, Qt, QTimer, pyqtBoundSignal, pyqtSlot
from PyQt5.QtGui import QCursor, QFont, QIcon
from PyQt5.QtWidgets import QHBoxLayout, QLabel, QPushButton, QSizePolicy, QWidget

from securedrop_client.db import File as DatabaseFile
from securedrop_client.gui import SecureQLabel
from securedrop_client.gui.conversation.export import Dialog as ExportDialog
from securedrop_client.gui.conversation.print import Dialog as PrintDialog
from securedrop_client.logic import Controller
from securedrop_client.resources import load_css, load_icon, load_movie
from securedrop_client.utils import humanize_filesize

logger = logging.getLogger(__name__)


class File(QWidget):
    """
    Represents a file.
    """

    DOWNLOAD_BUTTON_CSS = load_css("file_download_button.css")

    TOP_MARGIN = 18
    BOTTOM_MARGIN = 0
    FILE_FONT_SPACING = 2
    FILE_OPTIONS_FONT_SPACING = 1.6
    FILENAME_WIDTH_PX = 360
    FILE_OPTIONS_LAYOUT_SPACING = 8

    WIDTH_TO_CONTAINER_WIDTH_RATIO = 5 / 9
    MIN_CONTAINER_WIDTH = 750
    MIN_WIDTH = 400

    def __init__(
        self,
        file_uuid: str,
        controller: Controller,
        file_ready_signal: pyqtBoundSignal,
        file_missing: pyqtBoundSignal,
        index: int,
        container_width: int,
    ) -> None:
        """
        Given some text and a reference to the controller, make something to display a file.
        """
        super().__init__()

        self.controller = controller
        self.file = self.controller.get_file(file_uuid)
        self.uuid = file_uuid
        self.index = index
        self.downloading = False

        self.adjust_width(container_width)

        self.setObjectName("FileWidget")
        file_description_font = QFont()
        file_description_font.setLetterSpacing(QFont.AbsoluteSpacing, self.FILE_FONT_SPACING)
        self.file_buttons_font = QFont()
        self.file_buttons_font.setLetterSpacing(
            QFont.AbsoluteSpacing, self.FILE_OPTIONS_FONT_SPACING
        )

        # Set layout
        layout = QHBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        layout.setSpacing(0)

        # File options: download, export, print
        self.file_options = QWidget()
        self.file_options.setObjectName("FileWidget_file_options")
        file_options_layout = QHBoxLayout()
        self.file_options.setLayout(file_options_layout)
        file_options_layout.setContentsMargins(0, 0, 0, 0)
        file_options_layout.setSpacing(self.FILE_OPTIONS_LAYOUT_SPACING)
        file_options_layout.setAlignment(Qt.AlignLeft)
        self.download_button = QPushButton(_(" DOWNLOAD"))
        self.download_button.setObjectName("FileWidget_download_button")
        self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)
        self.download_button.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.download_button.setIcon(load_icon("download_file.svg"))
        self.download_button.setFont(self.file_buttons_font)
        self.download_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.download_animation = load_movie("download_file.gif")
        self.export_button = QPushButton(_("EXPORT"))
        self.export_button.setObjectName("FileWidget_export_print")
        self.export_button.setFont(self.file_buttons_font)
        self.export_button.setCursor(QCursor(Qt.PointingHandCursor))
        self.middot = QLabel("·")  # nosemgrep: semgrep.untranslated-gui-string
        self.print_button = QPushButton(_("PRINT"))
        self.print_button.setObjectName("FileWidget_export_print")
        self.print_button.setFont(self.file_buttons_font)
        self.print_button.setCursor(QCursor(Qt.PointingHandCursor))
        file_options_layout.addWidget(self.download_button)
        file_options_layout.addWidget(self.export_button)
        file_options_layout.addWidget(self.middot)
        file_options_layout.addWidget(self.print_button)

        self.download_button.installEventFilter(self)
        self.export_button.clicked.connect(self._on_export_clicked)
        self.print_button.clicked.connect(self._on_print_clicked)

        self.file_name = SecureQLabel(
            wordwrap=False, max_length=self.FILENAME_WIDTH_PX, with_tooltip=True
        )
        self.file_name.setObjectName("FileWidget_file_name")
        self.file_name.installEventFilter(self)
        self.file_name.setCursor(QCursor(Qt.PointingHandCursor))
        self.no_file_name = SecureQLabel(_("ENCRYPTED FILE ON SERVER"), wordwrap=False)
        self.no_file_name.setObjectName("FileWidget_no_file_name")
        self.no_file_name.setFont(file_description_font)

        # Line between file name and file size
        self.horizontal_line = QWidget()
        self.horizontal_line.setObjectName("FileWidget_horizontal_line")
        self.horizontal_line.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

        # Space between elided file name and file size when horizontal line is hidden
        self.spacer = QWidget()
        self.spacer.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.spacer.hide()

        # File size
        self.file_size = SecureQLabel(humanize_filesize(self.file.size))
        self.file_size.setObjectName("FileWidget_file_size")
        self.file_size.setAlignment(Qt.AlignRight)

        # Decide what to show or hide based on whether or not the file's been downloaded
        self._set_file_state()

        # Add widgets
        layout.addWidget(self.file_options)
        layout.addWidget(self.file_name)
        layout.addWidget(self.no_file_name)
        layout.addWidget(self.spacer)
        layout.addWidget(self.horizontal_line)
        layout.addWidget(self.file_size)

        # Connect signals to slots
        file_ready_signal.connect(self._on_file_downloaded, type=Qt.QueuedConnection)
        file_missing.connect(self._on_file_missing, type=Qt.QueuedConnection)

    def adjust_width(self, container_width: int) -> None:
        """
        This is a workaround to the workaround for https://bugreports.qt.io/browse/QTBUG-85498.
        See comment in the adjust_width method for SpeechBubble.
        """
        if container_width < self.MIN_CONTAINER_WIDTH:
            self.setFixedWidth(self.MIN_WIDTH)
        else:
            self.setFixedWidth(container_width * self.WIDTH_TO_CONTAINER_WIDTH_RATIO)

    def eventFilter(self, obj: QObject, event: QEvent) -> None:
        t = event.type()
        if t == QEvent.MouseButtonPress:
            if event.button() == Qt.LeftButton:
                self._on_left_click()
        elif t == QEvent.HoverEnter and not self.downloading:
            self.download_button.setIcon(load_icon("download_file_hover.svg"))
        elif t == QEvent.HoverLeave and not self.downloading:
            self.download_button.setIcon(load_icon("download_file.svg"))

        return QObject.event(obj, event)

    def update_file_size(self) -> None:
        try:
            self.file_size.setText(humanize_filesize(self.file.size))
        except Exception as e:
            logger.error(f"Could not update file size on FileWidget: {e}")
            self.file_size.setText("")

    def _set_file_state(self) -> None:
        if self.file.is_decrypted:
            logger.debug("Changing file {} state to decrypted/downloaded".format(self.uuid))
            self._set_file_name()
            self.download_button.hide()
            self.no_file_name.hide()
            self.export_button.show()
            self.middot.show()
            self.print_button.show()
            self.file_name.show()
            self.update_file_size()
        else:
            logger.debug("Changing file {} state to not downloaded".format(self.uuid))
            self.download_button.setText(_("DOWNLOAD"))

            # Ensure correct icon depending on mouse hover state.
            if self.download_button.underMouse():
                self.download_button.setIcon(load_icon("download_file_hover.svg"))
            else:
                self.download_button.setIcon(load_icon("download_file.svg"))

            self.download_button.setFont(self.file_buttons_font)
            self.download_button.show()

            # Reset stylesheet
            self.download_button.setStyleSheet("")
            self.download_button.setObjectName("FileWidget_download_button")
            self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)

            self.no_file_name.hide()
            self.export_button.hide()
            self.middot.hide()
            self.print_button.hide()
            self.file_name.hide()
            self.no_file_name.show()

    def _set_file_name(self) -> None:
        self.file_name.setText(self.file.filename)
        if self.file_name.is_elided():
            self.horizontal_line.hide()
            self.spacer.show()

    @pyqtSlot(str, str, str)
    def _on_file_downloaded(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.uuid:
            self.downloading = False
            QTimer.singleShot(300, self.stop_button_animation)

    @pyqtSlot(str, str, str)
    def _on_file_missing(self, source_uuid: str, file_uuid: str, filename: str) -> None:
        if file_uuid == self.uuid:
            self.downloading = False
            QTimer.singleShot(300, self.stop_button_animation)

    @pyqtSlot()
    def _on_export_clicked(self) -> None:
        """
        Called when the export button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        self.export_dialog = ExportDialog(self.controller, self.uuid, self.file.filename)
        self.export_dialog.show()

    @pyqtSlot()
    def _on_print_clicked(self) -> None:
        """
        Called when the print button is clicked.
        """
        if not self.controller.downloaded_file_exists(self.file):
            return

        dialog = PrintDialog(self.controller, self.uuid, self.file.filename)
        dialog.exec()

    def _on_left_click(self) -> None:
        """
        Handle a completed click via the program logic. The download state
        of the file distinguishes which function in the logic layer to call.
        """
        # update state
        self.file = self.controller.get_file(self.uuid)

        if self.file.is_decrypted:
            # Open the already downloaded and decrypted file.
            self.controller.on_file_open(self.file)
        elif not self.downloading:
            if self.controller.api:
                self.start_button_animation()
            # Download the file.
            self.controller.on_submission_download(DatabaseFile, self.uuid)

    def start_button_animation(self) -> None:
        """
        Update the download button to the animated "downloading" state.
        """
        self.downloading = True
        self.download_animation.frameChanged.connect(self.set_button_animation_frame)
        self.download_animation.start()
        self.download_button.setText(_(" DOWNLOADING "))

        # Reset widget stylesheet
        self.download_button.setStyleSheet("")
        self.download_button.setObjectName("FileWidget_download_button_animating")
        self.download_button.setStyleSheet(self.DOWNLOAD_BUTTON_CSS)

    def set_button_animation_frame(self, frame_number: int) -> None:
        """
        Sets the download button's icon to the current frame of the spinner
        animation.
        """
        self.download_button.setIcon(QIcon(self.download_animation.currentPixmap()))

    def stop_button_animation(self) -> None:
        """
        Stops the download animation and restores the button to its default state.
        """
        self.download_animation.stop()
        self.file = self.controller.get_file(self.file.uuid)
        self._set_file_state()
