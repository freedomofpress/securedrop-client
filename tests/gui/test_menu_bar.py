import unittest

from PyQt5.QtCore import Qt
from PyQt5.QtGui import QFocusEvent
from PyQt5.QtTest import QTest
from PyQt5.QtWidgets import QApplication, QWidget

from securedrop_client.gui import SDMenuBar

app = QApplication([])


class SDMenuBarTest(unittest.TestCase):
    def setUp(self):
        self.menubar = SDMenuBar()

    def test_sets_parent(self):
        parent = QWidget()
        menubar = SDMenuBar(parent)
        assert menubar.parent() == parent

    def test_has_no_parent_by_default(self):
        assert self.menubar.parent() is None

    def test_is_hidden_by_default(self):
        assert self.menubar.isHidden()

    def test_exposes_its_toggle_key(self):
        assert self.menubar.toggle_key() == Qt.Key_Alt

    def test_becomes_visible_when_toggle_key_is_pressed(self):
        # I couln't find a way to send "Alt" without sending another key as well.
        QTest.keyClicks(self.menubar, " ", Qt.AltModifier)
        assert self.menubar.isVisible()

    def test_when_visible_becomes_hidden_when_toggle_key_is_pressed(self):
        self.menubar.show()
        # I couln't find a way to send "Alt" without sending another key as well.
        QTest.keyClicks(self.menubar, " ", Qt.AltModifier)
        assert self.menubar.isHidden()

    @unittest.skip("I couldn't find how to emulate an Escape key event.")
    def test_becomes_hidden_when_close_key_is_pressed(self):
        self.menubar.show()
        QTest.keyClicks(self.menubar, " ")
        assert self.menubar.isHidden()

    def test_hides_automatically_when_loosing_focus(self):
        self.menubar.show()
        self.menubar.setFocus(True)
        self.menubar.focusOutEvent(QFocusEvent(QFocusEvent.FocusOut))
        assert self.menubar.isHidden()

    def test_does_not_hide_automatically_when_loosing_focus_because_menu_was_open(self):
        self.menubar.show()
        self.menubar.setFocus(True)
        self.menubar.focusOutEvent(QFocusEvent(QFocusEvent.FocusOut, Qt.PopupFocusReason))
        assert self.menubar.isVisible()
