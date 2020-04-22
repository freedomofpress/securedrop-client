import sys

from typing import Union

from PyQt5.QtCore import Qt, pyqtSlot, pyqtSignal
from PyQt5.QtWidgets import QApplication, QWidget, QLabel, QHBoxLayout, QVBoxLayout, QSizePolicy


class SecureQLabel(QLabel):
    def __init__(
        self,
        text: str = "",
        parent: QWidget = None,
        flags: Union[Qt.WindowFlags, Qt.WindowType] = Qt.WindowFlags(),
        wordwrap: bool = True,
        max_length: int = 0,
        with_tooltip: bool = False,
    ):
        super().__init__(parent, flags)
        self.wordwrap = wordwrap
        self.max_length = max_length
        self.setWordWrap(wordwrap)  # If True, wraps text at default of 70 characters
        self.with_tooltip = with_tooltip
        self.setText(text)
        self.elided = True if self.text() != text else False

    def setText(self, text: str) -> None:
        text = text.strip()
        self.setTextFormat(Qt.PlainText)
        elided_text = self.get_elided_text(text)
        self.elided = True if elided_text != text else False
        if self.elided and self.with_tooltip:
            tooltip_label = SecureQLabel(text)
            self.setToolTip(tooltip_label.text())
        super().setText(elided_text)

    def get_elided_text(self, full_text: str) -> str:
        if not self.max_length:
            return full_text

        # Only allow one line of elided text
        if '\n' in full_text:
            full_text = full_text.split('\n', 1)[0]

        fm = self.fontMetrics()
        filename_width = fm.horizontalAdvance(full_text)
        if filename_width > self.max_length:
            elided_text = ''
            for c in full_text:
                if fm.horizontalAdvance(elided_text) > self.max_length:
                    elided_text = elided_text[:-3] + '...'
                    return elided_text
                elided_text = elided_text + c

        return full_text

    def is_elided(self) -> bool:
        return self.elided


class SpeechBubble(QWidget):
    """
    Represents a speech bubble that's part of a conversation between a source
    and journalist.
    """

    CSS = '''
    #speech_bubble {
        min-width: 540px;
        max-width: 540px;
        background-color: #fff;
    }
    #message {
        font-family: 'Source Sans Pro';
        font-weight: 400;
        font-size: 15px;
        background-color: #fff;
        padding: 16px;
    }
    #color_bar {
        min-height: 5px;
        max-height: 5px;
        background-color: #102781;
        border: 0px;
    }
    '''

    TOP_MARGIN = 28
    BOTTOM_MARGIN = 10

    def __init__(self, message_uuid: str, text: str, update_signal, index: int) -> None:
        super().__init__()
        self.uuid = message_uuid
        self.index = index

        # Set styles
        self.setStyleSheet(self.CSS)
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        # Set layout
        layout = QVBoxLayout()
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Message box
        self.message = SecureQLabel(text)
        self.message.setObjectName('message')

        # Color bar
        self.color_bar = QWidget()
        self.color_bar.setObjectName('color_bar')

        # Speech bubble
        speech_bubble = QWidget()
        speech_bubble.setObjectName('speech_bubble')
        speech_bubble_layout = QVBoxLayout()
        speech_bubble.setLayout(speech_bubble_layout)
        speech_bubble_layout.addWidget(self.message)
        speech_bubble_layout.addWidget(self.color_bar)
        speech_bubble_layout.setContentsMargins(0, 0, 0, 0)
        speech_bubble_layout.setSpacing(0)

        # Bubble area includes speech bubble plus error message if there is an error
        bubble_area = QWidget()
        bubble_area.setLayoutDirection(Qt.RightToLeft)
        self.bubble_area_layout = QHBoxLayout()
        self.bubble_area_layout.setContentsMargins(0, self.TOP_MARGIN, 0, self.BOTTOM_MARGIN)
        bubble_area.setLayout(self.bubble_area_layout)
        self.bubble_area_layout.addWidget(speech_bubble)

        self.message.setTextInteractionFlags(Qt.TextSelectableByMouse)

        # Add widget to layout
        layout.addWidget(bubble_area)

        # Connect signals to slots
        #update_signal.connect(self._update_text)

    @pyqtSlot(str, str, str)
    def _update_text(self, source_id: str, message_uuid: str, text: str) -> None:
        """
        Conditionally update this SpeechBubble's text if and only if the message_uuid of the emitted
        signal matches the uuid of this speech bubble.
        """
        if message_uuid == self.uuid:
            self.message.setText(text)

    def mousePressEvent(self, e):
        clippy = QApplication.clipboard()
        self.message.setSelection(0, 10)
        clippy.setText(self.message.text())


if __name__ == '__main__':
    app = QApplication(sys.argv)

    """
    label = SecureQLabel('teehee')
    label.setTextInteractionFlags(Qt.TextSelectableByMouse)

    layout = QHBoxLayout()
    layout.addWidget(label)
    """

    blah = pyqtSignal(str)

    wid = SpeechBubble('teehee', 'teehee', blah, 0)
    # wid = QWidget()
    # wid.setLayout(layout)
    wid.show()

    sys.exit(app.exec_())
