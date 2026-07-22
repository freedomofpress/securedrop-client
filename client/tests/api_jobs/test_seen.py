from securedrop_client.api_jobs.seen import SeenJob
from tests import factory


def test_seen(homedir, mocker, session):
    """
    Check that the job makes the seen api request with the expected items.
    """
    api_client = mocker.MagicMock()
    file = factory.File()
    message = factory.Message()
    reply = factory.Reply()
    session.add(file)
    session.add(message)
    session.add(reply)

    job = SeenJob([file.uuid], [message.uuid], [reply.uuid])
    job.call_api(api_client, session)

    api_client.seen.assert_called_once_with([file.uuid], [message.uuid], [reply.uuid])


def test_seen_skips_making_request_if_no_items_to_mark_seen(homedir, mocker, session, source):
    """
    Check that the job does not make the seen api request if there are no items to mark as seen.
    """
    api_client = mocker.MagicMock()

    job = SeenJob([], [], [])
    job.call_api(api_client, session)

    api_client.seen.assert_not_called()


def test_seen_with_file_only(homedir, mocker, session, source):
    api_client = mocker.MagicMock()
    file = factory.File()
    session.add(file)

    job = SeenJob([file.uuid], [], [])
    job.call_api(api_client, session)

    api_client.seen.assert_called_once_with([file.uuid], [], [])


def test_seen_with_message_only(homedir, mocker, session, source):
    api_client = mocker.MagicMock()
    message = factory.Message()
    session.add(message)

    job = SeenJob([], [message.uuid], [])
    job.call_api(api_client, session)

    api_client.seen.assert_called_once_with([], [message.uuid], [])


def test_seen_with_reply_only(homedir, mocker, session, source):
    api_client = mocker.MagicMock()
    reply = factory.Reply()
    session.add(reply)

    job = SeenJob([], [], [reply.uuid])

    job.call_api(api_client, session)

    api_client.seen.assert_called_once_with([], [], [reply.uuid])
