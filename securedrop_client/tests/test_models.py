from securedrop_client.models import User


def test_string_representation_of_user():
    user = User('hehe')
    user.__repr__()
