from securedrop_client.models import User

import unittest


class ModelsTestCase(unittest.TestCase):
    def test_string_representation_of_user(self):
        user = User('hehe')
        user.__repr__()
