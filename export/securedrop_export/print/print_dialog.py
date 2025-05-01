import logging

import gi

gi.require_version("Gtk", "4.0")

from gi.repository import Gtk  # noqa: E402

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
        """On GUI startup"""
        window = Gtk.Window(application=app)
        self.dialog = Gtk.PrintUnixDialog.new(
            "Print Document",  # FIXME: this should be localized
            window
        )
        self.dialog.connect("response", self.on_response)
        self.dialog.show()
        window.hide()

    def on_response(self, parent_widget, response_id):
        """
        When the user clicks one of the print dialog's action buttons
        [ CANCEL ] [ PRINT ]
        """

        if response_id == Gtk.ResponseType.OK:  # Print
            settings = self.dialog.get_settings()
            printer = self.dialog.get_selected_printer()
            page_setup = self.dialog.get_page_setup()

            # GTK in bookworm has a bug in which page ranges are not properly
            # passed to IPP printers, we work around that by explicitly
            # passing them to CUPS, and disallowing multiple ranges.
            #   - https://gitlab.gnome.org/GNOME/gtk/-/issues/7528
            #   - https://gitlab.gnome.org/GNOME/gtk/-/issues/7527
            page_range_str = ""
            page_ranges = settings.get_page_ranges()
            if len(page_ranges) > 1:
                self.show_error_disallowed_range()
                return
            elif len(page_ranges) == 1:
                # `page_ranges` is 0-indexed, but CUPS wants the range to be 1-indexed
                start = page_ranges[0].start + 1
                end = page_ranges[0].end + 1

                if start == end:
                    page_range_str = str(start)
                else:
                    page_range_str = f"{start}-{end}"
                settings.set("cups-page-ranges", page_range_str)

            self.dialog.hide()
            job = Gtk.PrintJob.new(
                "print job",  # FIXME: this should be localized
                printer, settings, page_setup
            )
            job.set_source_file(self.file_to_print)
            job.send(self.on_job_complete, user_data=None)
        elif response_id == Gtk.ResponseType.APPLY:  # Preview (if available)
            pass
        elif response_id in (
            Gtk.ResponseType.CANCEL,  # Cancel button
            Gtk.ResponseType.DELETE_EVENT,  # Window closed
        ):
            self.quit()

    def on_job_complete(self, print_job, user_data, error):
        """
        When print dialog sends over the data to CUPS for printing. This does
        not necessarily mean that the file has been fully printed. At this
        point we just want the print dialog to disappear.
        """
        if error:
            # Error does not need to be communicated to the user
            #   - notifications already show current print issues
            #   - printer icon in tray menu shows print errors
            #   - future print dialogs display issues with a printer
            pass
        self.quit()  # Close print dialog and exit GTK application

    def show_error_disallowed_range(self):
        dialog = Gtk.MessageDialog(
            modal=True,
            message_type=Gtk.MessageType.ERROR,
            buttons=Gtk.ButtonsType.OK,
            text="Page Range Limitation",  # FIXME: this should be localized
            secondary_text="Providing multiple page ranges is not "
            "supported at this time.\nPlease use only one, e.g. \"2-4\".",
        )
        dialog.connect("response", lambda d, _: d.close())
        dialog.show()
