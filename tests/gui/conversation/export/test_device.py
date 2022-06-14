import unittest
from unittest import mock

from securedrop_client.gui.conversation import ExportDevice
from securedrop_client.logic import Controller


class ExportDeviceTest(unittest.TestCase):
    def test_controller_is_accessible_but_private(self):
        controller = mock.MagicMock(spec=Controller)
        device = ExportDevice(controller)

        # This is temporarily part of the Device interface.
        assert device._controller == controller
