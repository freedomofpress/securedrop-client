from securedrop_client.api_jobs.seen import SeenJob
from tests import factory


def test_seen(homedir, mocker, session, source):
    """
    Check if we call add_star method if a source is not stared.
    """
    file = factory.File(id=1, source=source["source"])
    message = factory.Message(id=2, source=source["source"])
    reply = factory.Reply(source=factory.Source())
    session.add(file)
    session.add(message)
    session.add(reply)

    api_client = mocker.MagicMock()

    job = SeenJob([file], [message], [reply])

    job.call_api(api_client, session)

    api_client.seen.assert_called_once_with([file], [message], [reply])
