from tests import factory
from securedrop_client.models import Reply, Submission, User
from unittest import mock


def test_string_representation_of_user():
    user = User('hehe')
    user.__repr__()


def test_string_representation_of_source():
    source = factory.Source()
    source.__repr__()


def test_string_representation_of_submission():
    source = factory.Source()
    submission = Submission(source=source, uuid="test", size=123,
                            filename="test.docx",
                            download_url='http://test/test')
    submission.__repr__()


def test_submission_content_not_downloaded():
    source = factory.Source()
    submission = Submission(source=source, uuid="test", size=123,
                            filename="test.docx",
                            download_url='http://test/test')
    assert submission.content is None


def test_submission_content_downloaded():
    source = factory.Source()
    submission = Submission(source=source, uuid="test", size=123,
                            filename="test.docx",
                            download_url='http://test/test')
    submission.is_downloaded = True
    with mock.patch('builtins.open', mock.mock_open(read_data="blah")):
        assert submission.content == "blah"


def test_reply_content_not_downloaded():
    source = factory.Source()
    journalist = User('Testy mcTestface')
    reply = Reply(source=source, uuid="test", size=123,
                  filename="test.docx", journalist=journalist)
    assert reply.content is None


def test_reply_content_downloaded():
    source = factory.Source()
    journalist = User('Testy mcTestface')
    reply = Reply(source=source, uuid="test", size=123,
                  filename="test.docx", journalist=journalist)
    reply.is_downloaded = True
    with mock.patch('builtins.open', mock.mock_open(read_data="blah")):
        assert reply.content == "blah"


def test_string_representation_of_reply():
    user = User('hehe')
    source = factory.Source()
    reply = Reply(source=source, journalist=user, filename="reply.gpg",
                  size=1234, uuid='test')
    reply.__repr__()


# test reply content xxx jt

def test_source_collection():
    # Create some test submissions and replies
    source = factory.Source()
    submission = Submission(source=source, uuid="test", size=123,
                            filename="2-test.doc.gpg",
                            download_url='http://test/test')
    user = User('hehe')
    reply = Reply(source=source, journalist=user, filename="1-reply.gpg",
                  size=1234, uuid='test')
    source.submissions = [submission]
    source.replies = [reply]

    # Now these items should be in the source collection in the proper order
    assert source.collection[0] == reply
    assert source.collection[1] == submission
