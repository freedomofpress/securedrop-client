"""
Contains the main widgets used by the client to display things in the UI.
"""
import logging
from PyQt5.QtWidgets import (QListWidget, QTextEdit, QLabel, QToolBar, QAction,
                             QWidget, QListWidgetItem, QHBoxLayout,
                             QVBoxLayout, QLineEdit, QPlainTextEdit)


logger = logging.getLogger(__name__)


class ToolBar(QWidget):
    """
    Represents the tool bar across the top of the user interface.
    """
    
    def __init__(self, parent):
        super().__init__(parent)
        self.setMaximumHeight(48)
        layout = QHBoxLayout(self)
        self.status = QLabel(_("Synchronized: 5 minutes ago."))
        self.user_state = QLabel(_("Logged in as: Testy McTestface"))
        layout.addWidget(self.status)
        layout.addStretch()
        layout.addWidget(self.user_state)


class MainView(QWidget):
    """
    Represents the main content of the application (containing the source list
    and main context view).
    """

    def __init__(self, parent):
        super().__init__(parent)
        self.layout = QHBoxLayout(self)
        self.setLayout(self.layout)
        left_column = QWidget(parent=self)
        left_layout = QVBoxLayout()
        left_column.setLayout(left_layout)
        filter_widget = QWidget()
        filter_layout = QHBoxLayout()
        filter_widget.setLayout(filter_layout)
        filter_label = QLabel(_('Filter: '))
        self.filter_term = QLineEdit()
        self.source_list = SourceList(left_column)
        filter_layout.addWidget(filter_label)
        filter_layout.addWidget(self.filter_term)
        left_layout.addWidget(filter_widget)
        left_layout.addWidget(self.source_list)
        self.layout.addWidget(left_column, 2)
        self.view_holder = QWidget()
        self.layout.addWidget(self.view_holder, 6)

    def update_view(self, widget):
        """
        Update the view holder to contain the referenced widget.
        """
        layout = QVBoxLayout()
        self.view_holder.setLayout(layout)
        layout.addWidget(widget)


class SourceList(QListWidget):
    """
    Represents the list of sources.
    """

    def __init__(self, parent):
        super().__init__(parent)

    def update(self, sources):
        """
        Reset and update the list with the passed in list of sources.
        """
        self.clear()
        for source in sources:
            new_source = SourceListItem(source, self)

class SourceListItem(QListWidgetItem):
    """
    Represents a source to be listed in the user interface.
    """

    def __init__(self, source, parent):
        super().__init__(parent)
        self.setText(source)
        #self.setIcon(load_icon(self.icon))

class SourceView(QPlainTextEdit):
    pass

class LoginView(QWidget):
    pass

class LogoutView(QWidget):
    pass
