import os
import shutil
import sys

from securedrop_export import export
from securedrop_export import main

CONFIG_PATH = "/etc/sd-export-config.json"

def start():
    my_sub = export.SDExport(sys.argv[1], CONFIG_PATH)
    try:
        # Halt immediately if target file is absent
        if not os.path.exists(my_sub.archive):
            msg = "ERROR_FILE_NOT_FOUND"
            my_sub.exit_gracefully(msg)
        main.__main__(my_sub)
        # Delete extracted achive from tempfile
        shutil.rmtree(my_sub.tmpdir)
    except Exception as e:
        # exit with 0 return code otherwise the os will attempt to open
        # the file with another application
        msg = "ERROR_GENERIC"
        my_sub.exit_gracefully(msg)
