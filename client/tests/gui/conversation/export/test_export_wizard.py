from unittest import mock

from securedrop_client.export_status import ExportStatus
from securedrop_client.gui.conversation.export import Export, ExportWizard
from securedrop_client.gui.conversation.export.export_wizard_constants import STATUS_MESSAGES, Pages
from securedrop_client.gui.conversation.export.export_wizard_page import (
    ErrorPage,
    FinalPage,
    InsertUSBPage,
    PassphraseWizardPage,
    PreflightPage,
)
from tests import factory


class TestExportWizard:
    @classmethod
    def _mock_export_preflight_success(cls) -> Export:
        export = Export()
        export.run_export_preflight_checks = lambda: export.export_state_changed.emit(
            ExportStatus.DEVICE_LOCKED
        )
        export.export = (
            mock.MagicMock()
        )  # We will choose different signals and emit them during testing
        return export

    @classmethod
    def setup_class(cls):
        cls.mock_controller = mock.MagicMock()
        cls.mock_controller.data_dir = "/pretend/data-dir/"
        cls.mock_source = factory.Source()
        cls.mock_export = cls._mock_export_preflight_success()
        cls.mock_file = factory.File(source=cls.mock_source)
        cls.filepath = cls.mock_file.location(cls.mock_controller.data_dir)

    @classmethod
    def setup_method(cls):
        cls.wizard = ExportWizard(cls.mock_export, cls.mock_file.filename, [cls.filepath])

    @classmethod
    def teardown_method(cls):
        cls.wizard.destroy()
        cls.wizard = None

    def test_wizard_setup(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        assert len(self.wizard.pageIds()) == len(Pages._member_names_), self.wizard.pageIds()
        assert isinstance(self.wizard.currentPage(), PreflightPage)

    def test_wizard_skips_insert_page_when_device_found_preflight(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        self.wizard.next()

        assert isinstance(self.wizard.currentPage(), PassphraseWizardPage)

    def test_wizard_exports_directly_to_unlocked_device(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        # Simulate an unlocked device
        self.mock_export.export_state_changed.emit(ExportStatus.DEVICE_WRITABLE)
        self.wizard.next()

        assert isinstance(
            self.wizard.currentPage(), FinalPage
        ), f"Actually, f{type(self.wizard.currentPage())}"

    def test_wizard_rewinds_if_device_removed(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), PassphraseWizardPage)

        self.mock_export.export_state_changed.emit(ExportStatus.NO_DEVICE_DETECTED)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), InsertUSBPage)

    def test_wizard_all_steps(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        self.mock_export.export_state_changed.emit(ExportStatus.NO_DEVICE_DETECTED)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), InsertUSBPage)

        self.mock_export.export_state_changed.emit(ExportStatus.MULTI_DEVICE_DETECTED)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), InsertUSBPage)
        assert self.wizard.currentPage().error_details.isVisible()

        self.mock_export.export_state_changed.emit(ExportStatus.DEVICE_LOCKED)
        self.wizard.next()
        page = self.wizard.currentPage()
        assert isinstance(page, PassphraseWizardPage)

        # No password entered, we shouldn't be able to advance
        self.wizard.next()
        assert isinstance(page, PassphraseWizardPage)

        # Type a passphrase. According to pytest-qt's own documentation, using
        # qtbot.keyClicks and other interactions can lead to flaky tests,
        # so using the setText method is fine, esp for unit testing.
        page.passphrase_field.setText("correct horse battery staple!")

        # How dare you try a commonly-used password like that
        self.mock_export.export_state_changed.emit(ExportStatus.ERROR_UNLOCK_LUKS)

        assert isinstance(page, PassphraseWizardPage)
        assert page.error_details.isVisible()

        self.wizard.next()

        # Ok
        page.passphrase_field.setText("substantial improvements encrypt accordingly")
        self.mock_export.export_state_changed.emit(ExportStatus.DEVICE_WRITABLE)

        self.wizard.next()
        self.mock_export.export_state_changed.emit(ExportStatus.ERROR_EXPORT_CLEANUP)

        page = self.wizard.currentPage()
        assert isinstance(page, FinalPage)
        assert page.body.text() == STATUS_MESSAGES.get(ExportStatus.ERROR_EXPORT_CLEANUP)

    def test_wizard_hides_error_details_on_success(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        self.mock_export.export_state_changed.emit(ExportStatus.NO_DEVICE_DETECTED)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), InsertUSBPage)
        assert self.wizard.currentPage().error_details.isVisible()

        self.mock_export.export_state_changed.emit(ExportStatus.DEVICE_LOCKED)
        self.wizard.next()
        self.wizard.back()
        assert not self.wizard.currentPage().error_details.isVisible()

    def test_wizard_only_shows_error_page_on_unrecoverable_error(self, qtbot):
        self.wizard.show()
        qtbot.addWidget(self.wizard)

        self.mock_export.export_state_changed.emit(ExportStatus.NO_DEVICE_DETECTED)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), InsertUSBPage)

        self.mock_export.export_state_changed.emit(ExportStatus.UNEXPECTED_RETURN_STATUS)
        self.wizard.next()
        assert isinstance(self.wizard.currentPage(), ErrorPage)
