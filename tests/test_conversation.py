import unittest
from datetime import datetime
from textwrap import dedent

from securedrop_client import conversation
from securedrop_client import db as database


class TestConversationTranscript(unittest.TestCase):
    def setUp(self):
        source = database.Source(
            journalist_designation="happy-bird",
        )
        files = [
            database.File(
                filename="4-memo.pdf.gpg",
                is_downloaded=True,
            ),
            database.File(
                filename="9-memo.zip.gpg",
                is_downloaded=True,
            ),
        ]
        messages = [
            database.Message(
                filename="1-message.gpg",
                is_downloaded=True,
                content="Hello! I think this is newsworthy: ...",
            ),
            database.Message(
                filename="6-message.gpg",
                is_downloaded=True,
                content="I can send you more if you're interested.",
            ),
            database.Message(
                filename="5-message.gpg",
                is_downloaded=True,
                content="Here is a document with details!",
            ),
            database.Message(
                filename="8-message.gpg",
                is_downloaded=True,
                content="Sure.",
            ),
        ]
        interested_journalist = database.User(username="interested-journalist")
        other_journalist = database.User(username="other-journalist")
        replies = [
            database.Reply(
                journalist=interested_journalist,
                filename="2-reply.gpg",
                is_downloaded=True,
                content=dedent(
                    """\
                    Thank you for the tip!

                    Can you tell me more about... ?
                    """
                ),
            ),
            database.Reply(
                journalist=interested_journalist,
                filename="3-reply.gpg",
                is_downloaded=True,
                content=dedent(
                    """\
                    Do you have proof of...?
                    """
                ),
            ),
            database.Reply(
                journalist=other_journalist,
                filename="7-reply.gpg",
                is_downloaded=True,
                content=dedent("Yes, the document you sent was useful, I'd love to see more."),
            ),
        ]
        draft_reply = database.DraftReply(
            content="Let me think...",
            file_counter=2,
            timestamp=datetime.now(),
        )
        source.files = files
        source.messages = messages
        source.replies = replies
        source.draftreplies = [draft_reply]

        self._source = source

    def test_indicates_explicitly_absence_of_messages(self):
        source = database.Source()
        assert str(conversation.Transcript(source)) == "No messages."

    def test_renders_all_messages(self):
        assert str(conversation.Transcript(self._source)) == dedent(
            """\
            happy-bird wrote:
            Hello! I think this is newsworthy: ...
            ------
            interested-journalist wrote:
            Thank you for the tip!

            Can you tell me more about... ?

            ------
            Do you have proof of...?

            ------
            happy-bird sent:
            File: 4-memo.pdf.gpg
            ------
            happy-bird wrote:
            Here is a document with details!
            ------
            I can send you more if you're interested.
            ------
            other-journalist wrote:
            Yes, the document you sent was useful, I'd love to see more.
            ------
            happy-bird wrote:
            Sure.
            ------
            happy-bird sent:
            File: 9-memo.zip.gpg
            """
        )
