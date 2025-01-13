import gi

gi.require_version("Gtk", "4.0")
import logging

from gi.repository import Gtk

from securedrop_export.exceptions import ExportException
from securedrop_export.print.status import Status

logger = logging.getLogger(__name__)

def open_print_dialog(file_to_print):
    app = PrintDialog(file_to_print)
    app.run()


class PrintDialog(Gtk.Application):
    def __init__(self, file_to_print):
        super().__init__(application_id="org.securedrop.PrintDialog")
        self.file_to_print = file_to_print
        self.connect("activate", self.on_activate)

    def on_activate(self, app):
        window = Gtk.Window(application=app)
        self.dialog = Gtk.PrintUnixDialog.new("Print Document", window)
        self.dialog.connect("response", self.on_response)
        self.dialog.show()
        window.hide()

    def on_response(self, parent_widget, response_id):
        if response_id == Gtk.ResponseType.OK:
            print(f"OK")
            self.dialog.hide()
            settings = self.dialog.get_settings()
            printer = self.dialog.get_selected_printer()
            page_setup = self.dialog.get_page_setup()
            job = Gtk.PrintJob.new("print job", printer, settings, page_setup)
            job.set_source_file(self.file_to_print)
            job.send(self.on_job_complete, user_data=None)
        elif response_id == Gtk.ResponseType.APPLY: # Preview (if available)
            pass
        elif response_id == Gtk.ResponseType.CANCEL:
            # FIXME should this exist or should it simply cancel and not report errors
            raise ExportException(sdstatus=Status.ERROR_PRINT, sderror="User canceled dialog")

    def on_job_complete(self, print_job, user_data, error):
        if error:
            self.quit()
            raise ExportException(sdstatus=Status.ERROR_PRINT, sderror=error.message)
