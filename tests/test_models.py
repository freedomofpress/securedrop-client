from securedrop_client.models import Reply, Source, Submission, User


def test_string_representation_of_user():
    user = User('hehe')
    user.__repr__()


def test_string_representation_of_source():
    source = Source(journalist_designation="testy test", uuid="test")
    source.__repr__()


def test_string_representation_of_submission():
    source = Source(journalist_designation="testy test", uuid="test")
    submission = Submission(source=source, uuid="test", filename="test.docx")
    submission.__repr__()


def test_string_representation_of_reply():
    user = User('hehe')
    source = Source(journalist_designation="testy test", uuid="test")
    reply = Reply(source=source, journalist=user, filename="reply.gpg",
                  size=1234)
    reply.__repr__()
