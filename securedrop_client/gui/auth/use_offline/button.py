from gettext import gettext as _

from securedrop_client.gui.base import SDPushButton


class LoginOfflineLink(SDPushButton):
    """A button that logs the user in, in offline mode."""

    def __init__(self) -> None:
        super().__init__()
        self.setText(_("USE OFFLINE"))
        self.setAlignment(SDPushButton.AlignLeft)
