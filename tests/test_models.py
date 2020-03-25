import datetime
import pytest

from tests import factory
from securedrop_client.db import DraftReply, Reply, File, Message, ReplySendStatus, User


def test_user_fullname():
    user1 = User(username='username_mock', firstname='firstname_mock', lastname='lastname_mock')
    user2 = User(username='username_mock', firstname='firstname_mock')
    user3 = User(username='username_mock', lastname='lastname_mock')
    user4 = User(username='username_mock')
    assert user1.fullname == 'firstname_mock lastname_mock'
    assert user2.fullname == 'firstname_mock'
    assert user3.fullname == 'lastname_mock'
    assert user4.fullname == 'username_mock'

    user1.__repr__()


def test_user_initials():
    # initials should be first char of firstname followed by first char of last name
    user1 = User(username='username_mock', firstname='firstname_mock', lastname='lastname_mock')
    user2 = User(username='username_mock', firstname='firstname_mock', lastname='l')
    user3 = User(username='username_mock', firstname='f', lastname='lastname_mock')
    user4 = User(username='username_mock', firstname='f', lastname='l')
    assert user1.initials == 'fl'
    assert user2.initials == 'fl'
    assert user3.initials == 'fl'
    assert user4.initials == 'fl'

    # initials should be first two chars of username
    user5 = User(username='username_mock')
    user6 = User(username='username_mock', firstname='f')
    user7 = User(username='username_mock', lastname='l')
    assert user5.initials == 'us'
    assert user6.initials == 'us'
    assert user7.initials == 'us'

    # initials should be first two chars of firstname or lastname
    user8 = User(username='username_mock', firstname='firstname_mock')
    user9 = User(username='username_mock', lastname='lastname_mock')
    assert user8.initials == 'fi'
    assert user9.initials == 'la'

    user1.__repr__()


def test_string_representation_of_source():
    source = factory.Source()
    source.__repr__()


def test_repr_representation_of_message():
    source = factory.Source()
    msg = Message(source=source, uuid="test", size=123, filename="1-test.docx",
                  download_url='http://test/test')
    msg.__repr__()


def test_repr_representation_of_file():
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="1-test.docx",
                 download_url='http://test/test')
    file_.__repr__()


def test_repr_representation_of_reply():
    user = User(username='hehe')
    source = factory.Source()
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    reply.__repr__()


def test_repr_representation_of_draft_reply():
    user = User(username='hehe')
    source = factory.Source()
    draft_reply = DraftReply(source=source, journalist=user, uuid='test')
    draft_reply.__repr__()


def test_string_representation_of_message():
    source = factory.Source()
    msg = Message(source=source, uuid="test", size=123, filename="1-test.docx",
                  download_url='http://test/test')
    msg.__str__()
    msg.content = "hello"
    msg.__str__()


def test_string_representation_of_file():
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="1-test.docx",
                 download_url='http://test/test')
    file_.__str__()
    file_.is_downloaded = True
    file_.__str__()


def test_string_representation_of_reply():
    user = User(username='hehe')
    source = factory.Source()
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    reply.__str__()
    reply.content = "hello"
    reply.__str__()


def test_string_representation_of_draft_reply():
    user = User(username='hehe')
    source = factory.Source()
    draft_reply = DraftReply(source=source, journalist=user, uuid='test')
    draft_reply.__str__()
    draft_reply.content = "hello"
    draft_reply.__str__()


def test_string_representation_of_send_reply_status():
    reply_status = ReplySendStatus(name='teehee')
    reply_status.__repr__()


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


def test_source_server_collection():
    # Create some test submissions and replies
    source = factory.Source()
    file_ = File(source=source, uuid="test", size=123, filename="2-test.doc.gpg",
                 download_url='http://test/test')
    message = Message(source=source, uuid="test", size=123, filename="3-test.doc.gpg",
                      download_url='http://test/test')
    user = User(username='hehe')
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    draft_reply = DraftReply(source=source, journalist=user,
                             uuid='test',
                             timestamp=datetime.datetime(2002, 6, 6, 6, 0))
    source.files = [file_]
    source.messages = [message]
    source.replies = [reply]
    source.draftreplies = [draft_reply]

    # Now these items should be in the source collection in the proper order
    assert source.server_collection[0] == reply
    assert source.server_collection[1] == file_
    assert source.server_collection[2] == message

    # Drafts do not appear in the server_collection, they are local only.
    assert draft_reply not in source.server_collection


def test_source_collection_ordering_with_multiple_draft_replies():
    # Create some test submissions, replies, and draft replies.
    source = factory.Source()
    file_1 = File(source=source, uuid="test", size=123, filename="1-test.doc.gpg",
                  download_url='http://test/test')
    message_2 = Message(source=source, uuid="test", size=123, filename="2-test.doc.gpg",
                        download_url='http://test/test')
    user = User(username='hehe')
    reply_3 = Reply(source=source, journalist=user, filename="3-reply.gpg",
                    size=1234, uuid='test')
    draft_reply_4 = DraftReply(uuid='4', source=source, journalist=user, file_counter=3,
                               timestamp=datetime.datetime(2000, 6, 6, 6, 0))
    draft_reply_5 = DraftReply(uuid='5', source=source, journalist=user, file_counter=3,
                               timestamp=datetime.datetime(2001, 6, 6, 6, 0))
    reply_6 = Reply(source=source, journalist=user, filename="4-reply.gpg",
                    size=1234, uuid='test2')
    draft_reply_7 = DraftReply(uuid='6', source=source, journalist=user, file_counter=4,
                               timestamp=datetime.datetime(2002, 6, 6, 6, 0))
    source.files = [file_1]
    source.messages = [message_2]
    source.replies = [reply_3, reply_6]
    source.draftreplies = [draft_reply_4, draft_reply_5, draft_reply_7]

    # Now these items should be in the source collection in the proper order
    assert source.collection[0] == file_1
    assert source.collection[1] == message_2
    assert source.collection[2] == reply_3
    assert source.collection[3] == draft_reply_4
    assert source.collection[4] == draft_reply_5
    assert source.collection[5] == reply_6
    assert source.collection[6] == draft_reply_7


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
