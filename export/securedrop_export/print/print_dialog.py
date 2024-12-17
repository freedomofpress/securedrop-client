import gi
gi.require_version("Gtk", "4.0")
from gi.repository import Gtk, Gio

import sys


def open_print_dialog():
    app = PrintDialog()
    app.run()


class PrintDialog(Gtk.Application):
    def __init__(self):
        super().__init__(application_id="org.securedrop.PrintDialog")
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
            job.set_source_file("/home/user/dangerzone/tests/test_docs/sample-pdf.pdf")
            job.send(self.on_job_complete, user_data=None)
        elif response_id == Gtk.ResponseType.APPLY: # Preview (if available)
            pass
        elif response_id == Gtk.ResponseType.CANCEL:
            pass

    def on_job_complete(self, print_job, user_data, error):
        print(f"ERROR {error}")
