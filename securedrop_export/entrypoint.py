import os
import shutil
import sys

from securedrop_export import export
from securedrop_export import main


def start():
    my_sub = export.SDExport(sys.argv[1])
    try:
        # Halt immediately if target file is absent
        if not os.path.exists(my_sub.archive):
            msg = "File does not exist"
            my_sub.exit_gracefully(msg)
        main.__main__(my_sub)
        # Delete extracted achive from tempfile
        shutil.rmtree(my_sub.tmpdir)
    except Exception as e:
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        msg = "Unhandled exception:"
        my_sub.exit_gracefully(msg, e=e)
