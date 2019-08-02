from securedrop_export import export


def __main__(submission):
    submission.extract_tarball()

    try:
        submission.archive_metadata = export.Metadata(submission.tmpdir)
    except Exception:
        submission.exit_gracefully("ERROR_METADATA_PARSING")

    if submission.archive_metadata.is_valid():
        if submission.archive_metadata.export_method == "usb-test":
            submission.check_usb_connected()
        elif submission.archive_metadata.export_method == "disk":
            # exports all documents in the archive to luks-encrypted volume
            submission.unlock_luks_volume(submission.archive_metadata.encryption_key)
            submission.mount_volume()
            submission.copy_submission()
        elif submission.archive_metadata.export_method == "disk-test":
            submission.check_luks_volume()
        elif submission.archive_metadata.export_method == "printer":
            # prints all documents in the archive
            printer_uri = submission.get_printer_uri()
            printer_ppd = submission.install_printer_ppd(printer_uri)
            submission.setup_printer(printer_uri, printer_ppd)
            submission.print_all_files()
        elif submission.archive_metadata.export_method == "printer-test":
            # Prints a test page to ensure the printer is functional
            printer_uri = submission.get_printer_uri()
            printer_ppd = submission.install_printer_ppd(printer_uri)
            submission.setup_printer(printer_uri, printer_ppd)
            submission.print_test_page()
    else:
        submission.exit_gracefully("ERROR_ARCHIVE_METADATA")
