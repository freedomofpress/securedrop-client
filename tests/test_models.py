from securedrop_client.models import Reply, Source, Submission, User


def test_string_representation_of_user():
    user = User('hehe')
    assert user.__repr__() == f'<Journalist: {user.username}>'


def test_string_representation_of_source():
    source = Source(journalist_designation="testy test", uuid="test",
                    is_flagged=False, public_key='test', interaction_count=1,
                    is_starred=False, last_updated='test')
    assert source.__repr__() == f'<Source {source.journalist_designation}>'


def test_string_representation_of_submission():
    source = Source(journalist_designation="testy test", uuid="test",
                    is_flagged=False, public_key='test', interaction_count=1,
                    is_starred=False, last_updated='test')
    submission = Submission(source=source, uuid="test", filename="test.docx")
    assert submission.__repr__() == f'<Submission {submission.filename}>'


def test_string_representation_of_reply():
    user = User('hehe')
    source = Source(journalist_designation="testy test", uuid="test",
                    is_flagged=False, public_key='test', interaction_count=1,
                    is_starred=False, last_updated='test')
    reply = Reply(source=source, journalist=user, filename="reply.gpg",
                  size=1234)
    assert reply.__repr__() == f'<Reply {reply.filename}>'
