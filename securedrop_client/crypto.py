"""
Copyright (C) 2018  The Freedom of the Press Foundation.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

import gzip
import logging
import os
import shutil
import subprocess
import tempfile


logger = logging.getLogger(__name__)


def decrypt_submission_or_reply(filepath, target_filename, home_dir,
                                is_qubes=True, is_doc=False):
    out = tempfile.NamedTemporaryFile(suffix=".message")
    err = tempfile.NamedTemporaryFile(suffix=".message-error", delete=False)
    if is_qubes:
        gpg_binary = "qubes-gpg-client"
    else:
        gpg_binary = "gpg"
    cmd = [gpg_binary, "--decrypt", filepath]
    res = subprocess.call(cmd, stdout=out, stderr=err)

    os.unlink(filepath)  # original file

    if res != 0:
        # The out tempfile will be automatically deleted after closing.
        out.close()
        # The err tempfile was created with delete=False, so needs to
        # be explicitly cleaned up. We will do that after we've read the file.
        err.close()

        with open(err.name) as e:
            msg = e.read()
            logger.error("GPG error: {}".format(msg))

        os.unlink(err.name)
        dest = ""
    else:
        # Cleanup err file
        err.close()
        os.unlink(err.name)

        if is_doc:
            # Docs are gzipped, so gunzip the file
            with gzip.open(out.name, 'rb') as infile:
                unzipped_decrypted_data = infile.read()

            # Need to split twice as filename is e.g.
            # 1-impractical_thing-doc.gz.gpg
            fn_no_ext, _ = os.path.splitext(
                os.path.splitext(os.path.basename(filepath))[0])
            dest = os.path.join(home_dir, "data", fn_no_ext)

            with open(dest, 'wb') as outfile:
                outfile.write(unzipped_decrypted_data)
        else:
            fn_no_ext, _ = os.path.splitext(target_filename)
            dest = os.path.join(home_dir, "data", fn_no_ext)
            shutil.copy(out.name, dest)

        # Now close to automatically delete the out tempfile.
        out.close()
        logger.info("Downloaded and decrypted: {}".format(dest))

    return res, dest
