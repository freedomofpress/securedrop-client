import logging
from PyQt5.QtWidgets import QMainWindow, QWidget, QVBoxLayout, QDesktopWidget
from securedrop_client import __version__
from securedrop_client.gui.widgets import *


logger = logging.getLogger(__name__)


class Window(QMainWindow):
    """
    Represents the application's main window that will contain the UI widgets.

    All interactions with the IU go through the object created by this class.
    """

    title = _("SecureDrop Client {}").format(__version__)
    
    def setup(self):
        """
        Create the default start state:

        * Not logged in.
        * Display current state of synced data.

        The window contains a root widget into which is placed:

        * A status bar widget at the top, containing curent user / status
          information.
        * A main-view widget, itself containing a list view for sources and a
          place for details / message contents / forms.
        """
        # self.setWindowIcon(load_icon(self.icon))
        self.widget = QWidget()
        widget_layout = QVBoxLayout()
        self.widget.setLayout(widget_layout)
        self.tool_bar = ToolBar(self.widget)
        self.main_view = MainView(self.widget)
        widget_layout.addWidget(self.tool_bar, 1)
        widget_layout.addWidget(self.main_view, 6)
        self.setCentralWidget(self.widget)
        self.main_view.source_list.update(['Benign Artichoke', 'Last Unicorn',
                                           'Jocular Beehive',
                                           'Sanitary Lemming'])
        self.main_view.update_view(SourceView())
        self.show()
        self.autosize_window()

    def autosize_window(self):
        """
        Makes the editor 80% of the width*height of the screen and centres it.
        """
        screen = QDesktopWidget().screenGeometry()
        w = int(screen.width() * 0.8)
        h = int(screen.height() * 0.8)
        self.resize(w, h)
        size = self.geometry()
        self.move((screen.width() - size.width()) / 2,
                  (screen.height() - size.height()) / 2)

    def show_login(self, error=False):
        pass

    def show_logout(self):
        pass

    def update_list(self, items):
        pass

    def show_source(self, source):
        pass

    def update_view(self, widget):
        pass
