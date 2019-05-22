import pytest

from tests import factory
from securedrop_client.db import Reply, File, Message, User


def test_string_representation_of_user():
    user = User(username='hehe')
    user.__repr__()


def test_string_representation_of_source():
    source = factory.Source()
    source.__repr__()


def test_string_representation_of_message():
    source = factory.Source()
    msg = Message(source=source, uuid="test", size=123, filename="1-test.docx",
                  download_url='http://test/test')
    msg.__repr__()


def test_string_representation_of_file():
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="1-test.docx",
                 download_url='http://test/test')
    file_.__repr__()


def test_string_representation_of_reply():
    user = User(username='hehe')
    source = factory.Source()
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    reply.__repr__()


def test_source_collection():
    # Create some test submissions and replies
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="2-test.doc.gpg",
                 download_url='http://test/test')
    message = Message(source=source, uuid="test", size=123, filename="3-test.doc.gpg",
                      download_url='http://test/test')
    user = User(username='hehe')
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    source.files = [file_]
    source.messages = [message]
    source.replies = [reply]

    # Now these items should be in the source collection in the proper order
    assert source.collection[0] == reply
    assert source.collection[1] == file_
    assert source.collection[2] == message


def test_file_init():
    '''
    Check that:
      - We can't pass the file_counter attribute
      - The file_counter attribute is see correctly based off the filename
    '''
    with pytest.raises(TypeError):
        File(file_counter=1)

    f = File(filename="1-foo")
    assert f.file_counter == 1


def test_message_init():
    '''
    Check that:
      - We can't pass the file_counter attribute
      - The file_counter attribute is see correctly based off the filename
    '''
    with pytest.raises(TypeError):
        Message(file_counter=1)

    m = Message(filename="1-foo")
    assert m.file_counter == 1


def test_reply_init():
    '''
    Check that:
      - We can't pass the file_counter attribute
      - The file_counter attribute is see correctly based off the filename
    '''
    with pytest.raises(TypeError):
        Reply(file_counter=1)

    r = Reply(filename="1-foo")
    assert r.file_counter == 1
