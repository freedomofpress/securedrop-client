"""
A dialog that allows users to sign in, or use the application offline.

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

from PyQt5.QtCore import QSize, Qt
from PyQt5.QtGui import QBrush, QPalette
from PyQt5.QtWidgets import (
    QDialog,
    QGraphicsOpacityEffect,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QSizePolicy,
    QVBoxLayout,
    QWidget,
)

from securedrop_client import __version__
from securedrop_client.gui.auth.sign_in import LoginErrorBar, SignInButton
from securedrop_client.gui.auth.use_offline import LoginOfflineLink
from securedrop_client.gui.base import PasswordEdit
from securedrop_client.gui.base.checkbox import SDCheckBox
from securedrop_client.logic import Controller
from securedrop_client.resources import load_image, load_relative_css

logger = logging.getLogger(__name__)


class LoginDialog(QDialog):
    """
    A dialog to display the login form.
    """

    MIN_PASSWORD_LEN = 14  # Journalist.MIN_PASSWORD_LEN on server
    MAX_PASSWORD_LEN = 128  # Journalist.MAX_PASSWORD_LEN on server
    MIN_JOURNALIST_USERNAME = 3  # Journalist.MIN_USERNAME_LEN on server

    def __init__(self, parent: QWidget) -> None:
        super().__init__(parent)

        # Set modal
        self.setModal(True)

        # Set layout
        layout = QVBoxLayout(self)
        self.setLayout(layout)

        # Set margins and spacing
        layout.setContentsMargins(0, 274, 0, 20)
        layout.setSpacing(0)

        # Set background
        self.setAutoFillBackground(True)
        palette = QPalette()
        palette.setBrush(QPalette.Background, QBrush(load_image("login_bg.svg")))
        self.setPalette(palette)
        self.setFixedSize(QSize(596, 671))  # Set to size provided in the login_bg.svg file
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        # Create error bar
        self.error_bar = LoginErrorBar()

        # Create form widget
        form = QWidget()

        form.setObjectName("LoginDialog_form")
        self.setStyleSheet(load_relative_css(__file__, "dialog.css"))

        form_layout = QVBoxLayout()
        form.setLayout(form_layout)

        form_layout.setContentsMargins(80, 0, 80, 0)
        form_layout.setSpacing(8)

        self.username_label = QLabel(_("Username"))
        self.username_field = QLineEdit()

        self.password_label = QLabel(_("Passphrase"))
        self.password_field = PasswordEdit(self)

        self.check = SDCheckBox()
        self.check.checkbox.stateChanged.connect(self.password_field.on_toggle_password_Action)

        self.tfa_label = QLabel(_("Two-Factor Code"))
        self.tfa_field = QLineEdit()

        self.opacity_effect = QGraphicsOpacityEffect()

        buttons = QWidget()
        buttons_layout = QHBoxLayout()
        buttons.setLayout(buttons_layout)
        buttons_layout.setContentsMargins(0, 20, 0, 0)
        self.submit = SignInButton()
        self.submit.clicked.connect(self.validate)
        self.offline_mode = LoginOfflineLink()
        buttons_layout.addWidget(self.offline_mode)
        buttons_layout.addStretch()
        buttons_layout.addWidget(self.submit)

        form_layout.addWidget(self.username_label)
        form_layout.addWidget(self.username_field)
        form_layout.addWidget(QWidget(self))
        form_layout.addWidget(self.password_label)
        form_layout.addWidget(self.password_field)
        form_layout.addWidget(self.check, alignment=Qt.AlignRight)
        form_layout.addWidget(self.tfa_label)
        form_layout.addWidget(self.tfa_field)
        form_layout.addWidget(buttons)

        # Create widget to display application name and version
        application_version = QLabel(_("SecureDrop Client v{}").format(__version__))
        application_version.setAlignment(Qt.AlignHCenter)
        application_version.setObjectName("LoginDialog_app_version_label")

        # Add widgets
        layout.addWidget(self.error_bar)
        layout.addStretch()
        layout.addWidget(form)
        layout.addStretch()
        layout.addWidget(application_version)

        self.submit.setDefault(True)

    def setup(self, controller: Controller) -> None:
        self.controller = controller
        self.offline_mode.clicked.connect(self.controller.login_offline_mode)

    def reset(self) -> None:
        """
        Resets the login form to the default state.
        """
        self.username_field.setText("")
        self.username_field.setFocus()
        self.password_field.setText("")
        self.tfa_field.setText("")
        self.setDisabled(False)
        self.error_bar.clear_message()

    def error(self, message: str) -> None:
        """
        Ensures the passed in message is displayed as an error message.
        """
        self.setDisabled(False)
        self.submit.setText(_("SIGN IN"))
        self.error_bar.set_message(message)

        self.opacity_effect.setOpacity(1)
        self.offline_mode.setGraphicsEffect(self.opacity_effect)

    def validate(self) -> None:
        """
        Validate the user input -- we expect values for:

        * username (free text)
        * password (free text)
        * TFA token (numerals)
        """
        self.setDisabled(True)
        username = self.username_field.text()
        password = self.password_field.text()
        tfa_token = self.tfa_field.text().replace(" ", "")
        if username and password and tfa_token:
            # Validate username
            if len(username) < self.MIN_JOURNALIST_USERNAME:
                self.setDisabled(False)
                self.error(
                    _("That username won't work.\n" "It should be at least 3 characters long.")
                )
                return

            # Validate password
            if len(password) < self.MIN_PASSWORD_LEN or len(password) > self.MAX_PASSWORD_LEN:
                self.setDisabled(False)
                self.error(
                    _(
                        "That passphrase won't work.\n"
                        "It should be between 14 and 128 characters long."
                    )
                )
                return

            # Validate 2FA token
            try:
                int(tfa_token)
            except ValueError:
                self.setDisabled(False)
                self.error(
                    _("That two-factor code won't work.\n" "It should only contain numerals.")
                )
                return
            self.submit.setText(_("SIGNING IN"))

            # Changing the opacity of the link to .4 alpha of its' 100% value when authenticated
            self.opacity_effect.setOpacity(0.4)
            self.offline_mode.setGraphicsEffect(self.opacity_effect)

            # If authentication is successful, clear error messages displayed priorly
            self.error_bar.clear_message()

            self.controller.login(username, password, tfa_token)
        else:
            self.setDisabled(False)
            self.error(_("Please enter a username, passphrase and " "two-factor code."))
