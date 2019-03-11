from tests import factory
from securedrop_client.db import Reply, File, Message, User


def test_string_representation_of_user():
    user = User('hehe')
    user.__repr__()


def test_string_representation_of_source():
    source = factory.Source()
    source.__repr__()


def test_string_representation_of_message():
    source = factory.Source()
    msg = Message(source=source, uuid="test", size=123, filename="test.docx",
                  download_url='http://test/test')
    msg.__repr__()


def test_string_representation_of_file():
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="test.docx",
                 download_url='http://test/test')
    file_.__repr__()


def test_string_representation_of_reply():
    user = User('hehe')
    source = factory.Source()
    reply = Reply(source=source, journalist=user, filename="reply.gpg",
                  size=1234, uuid='test')
    reply.__repr__()


def test_source_collection():
    # Create some test submissions and replies
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="2-test.doc.gpg",
                 download_url='http://test/test')
    message = Message(source=source, uuid="test", size=123, filename="3-test.doc.gpg",
                      download_url='http://test/test')
    user = User('hehe')
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    source.files = [file_]
    source.messages = [message]
    source.replies = [reply]

    # Now these items should be in the source collection in the proper order
    assert source.collection[0] == reply
    assert source.collection[1] == file_
    assert source.collection[2] == message
