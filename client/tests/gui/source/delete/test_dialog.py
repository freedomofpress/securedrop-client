import pytest

from securedrop_client.gui.source.delete import DeleteSourceDialog
from tests import factory


@pytest.fixture(
    params=[[], [factory.Source()], [factory.Source(), factory.Source()]],
)
def dialog(request):
    """
    Set up the dialog under various conditions: 0 sources, 1 source, >1 source.
    Tests that target a specific configuration can use decorators to skip unwanted
    conditions.
    """
    # Give the source(s) a submission
    for source in request.param:
        factory.File(source=source)
    return DeleteSourceDialog(request.param, len(request.param) + 1)


class TestDeleteSourceDialog:
    def test_dialog_setup(self, dialog):
        assert type(dialog) is DeleteSourceDialog
        assert type(dialog.sources) is list
        assert dialog.dangerous

    def test_default_button_is_safer_choice(self, dialog):
        # This test does rely on an implementation detail (the buttons)
        # but I couldn't find a way to test this properly using key events.
        assert not dialog.continue_button.isDefault()
        assert dialog.cancel_button.isDefault()

    def test_displays_important_information_when_shown(self, dialog):
        if len(dialog.sources) < 1:
            pytest.skip("Skip if no sources")
        assert "not be able to send them replies" in dialog.text()
        assert "source will not be able to log in" in dialog.text()
        assert "files and messages from that source will also be destroyed" in dialog.text()

    def test_dialog_continue_button_adapts_to_source_count(self, dialog):
        count = len(dialog.sources)

        if count < 1:
            pytest.skip("Skip if no sources")

        if count == 1:
            assert dialog.continue_button.text() == "YES, DELETE ENTIRE SOURCE ACCOUNT"
        elif count > 1:
            assert dialog.continue_button.text() == f"YES, DELETE {count} SOURCE ACCOUNTS"
        else:
            # should be unreachable due to decorator
            pytest.fail("Unreachable, or so we thought")

    def test_no_sources_shows_error_text(self, dialog):
        if len(dialog.sources) > 0:
            pytest.skip("Skip if sources")

        assert dialog.text() == "No sources have been selected."

    def test_no_sources_continue_button_not_shown(self, dialog):
        if len(dialog.sources) > 0:
            pytest.skip("Skip if sources")

        assert not dialog.continue_button.isEnabled()
        assert not dialog.continue_button.isVisible()

    def test_correct_format_body_text(self):
        """
        For n > 1 sources, ensure the warning text includes
        all the journalist designators.
        """
        sources = []
        names = [
            "source one",
            "source two",
            "source three",
        ]

        for item in names:
            source = factory.Source(journalist_designation=item)
            sources.append(source)
            # pretend we've selected all but one source
            fake_total = len(sources) + 1

        dialog = DeleteSourceDialog(sources, fake_total)
        dialog_text = dialog.make_body_text(sources, fake_total)

        assert "All sources have been selected" not in dialog_text
        for n in names:
            assert n in dialog_text

    def test_correct_format_body_text_all_selected(self):
        """
        Ensure that warning has been added when all sources selected
        """
        sources = []
        names = [
            "source one",
            "source two",
            "source three",
        ]

        for item in names:
            source = factory.Source(journalist_designation=item)
            sources.append(source)

        dialog = DeleteSourceDialog(sources, len(sources))

        assert "All sources have been selected" in dialog.make_body_text(sources, len(sources))

    def test_correct_format_body_text_truncated(self):
        """
        Ensure that source list is truncated correctly when over display limit
        """
        sources = []
        names = [f"source_{i}" for i in range(1, 46)]

        for item in names:
            source = factory.Source(journalist_designation=item)
            sources.append(source)

        dialog = DeleteSourceDialog(sources, len(sources))

        assert "plus 15 additional sources" in dialog.make_body_text(sources, len(sources))
