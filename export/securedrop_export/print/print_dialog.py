import gi

gi.require_version("Gtk", "4.0")
import logging

from gi.repository import Gtk

from securedrop_export.exceptions import ExportException
from securedrop_export.print.status import Status

logger = logging.getLogger(__name__)


class GtkExceptionRaiser:
    """
    Context manager to keep track of exceptions to be raised after GTK exits

    This is a workaround for the fact that GTK does not behave like regular
    libraries. Exceptions raised by the GUI code are always caught within GTK.
    The context manager provides a way to store these exceptions.

    Usage:

        class SomeApplication(Gtk.Application):
            def __init__(self, raise_later_func):
                super().__init__()
                self.raise_later_func = raise_later_func

            [...]

            def on_something_bad_happening(self):
                self.raise_later_func(Exception("something happned"))
                self.quit()

        with GtkExceptionRaiser() as raise_later_func:
            app = SomeApplication(raise_later_func)
            app.run()
    """

    def __init__(self):
        self.exception_to_raise = None

    def raise_later_func(self, exception):
        self.exception_to_raise = exception

    def __enter__(self):
        return self.raise_later_func

    def __exit__(self, exc_type, exc_val, exc_tb):
        if self.exception_to_raise:
            raise self.exception_to_raise


class PrintDialog(Gtk.Application):
    def __init__(self, file_to_print, raise_later_func):
        super().__init__(application_id="org.securedrop.PrintDialog")
        self.file_to_print = file_to_print
        self.raise_later_func = raise_later_func
        self.connect("activate", self.on_activate)

    def on_activate(self, app):
        window = Gtk.Window(application=app)
        window.hide()
        self.dialog = Gtk.PrintUnixDialog.new("Print Document", window)
        self.dialog.connect("response", self.on_response)
        self.dialog.connect("close", self.quit)
        self.dialog.show()

    def on_response(self, parent_widget, response_id):
        if response_id == Gtk.ResponseType.OK:
            self.dialog.hide()
            settings = self.dialog.get_settings()
            printer = self.dialog.get_selected_printer()
            page_setup = self.dialog.get_page_setup()
            job = Gtk.PrintJob.new("print job", printer, settings, page_setup)
            job.set_source_file(self.file_to_print)
            job.send(self.on_job_complete, user_data=None)
        elif response_id == Gtk.ResponseType.CANCEL:
            # FIXME should this exist or should it simply cancel and not report errors
            self.raise_later_func(
                ExportException(sdstatus=Status.ERROR_PRINT, sderror="User canceled dialog")
            )
            self.quit()
        elif response_id == Gtk.ResponseType.DELETE_EVENT:
            self.quit()

    def on_job_complete(self, print_job, user_data, error):
        if error:
            self.raise_later_func(
                ExportException(sdstatus=Status.ERROR_PRINT, sderror=error.message)
            )
        self.quit()


def open_print_dialog(file_to_print):
    with GtkExceptionRaiser() as raise_later_func:
        app = PrintDialog(file_to_print, raise_later_func)
        app.run()
