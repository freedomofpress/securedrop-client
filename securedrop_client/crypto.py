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

from securedrop_client.utils import safe_mkdir

logger = logging.getLogger(__name__)


class CryptoError(Exception):

    pass


class GpgHelper:

    def __init__(self, sdc_home: str, is_qubes: bool) -> None:
        '''
        :param sdc_home: Home directory for the SecureDrop client
        :param is_qubes: Whether the client is running in Qubes or not
        '''
        safe_mkdir(os.path.join(sdc_home), "gpg")
        self.sdc_home = sdc_home
        self.is_qubes = is_qubes

    def decrypt_submission_or_reply(self, filepath, target_filename, is_doc=False) -> None:
        err = tempfile.NamedTemporaryFile(suffix=".message-error", delete=False)
        with tempfile.NamedTemporaryFile(suffix=".message") as out:
            if self.is_qubes:  # pragma: no cover
                cmd = ["qubes-gpg-client"]
            else:
                cmd = ["gpg", "--homedir", os.path.join(self.sdc_home, "gpg")]

            cmd.extend(["--decrypt", filepath])
            res = subprocess.call(cmd, stdout=out, stderr=err)

            os.unlink(filepath)  # original file

            if res != 0:
                # The err tempfile was created with delete=False, so needs to
                # be explicitly cleaned up. We will do that after we've read the file.
                err.close()

                with open(err.name) as e:
                    msg = "GPG Error: {}".format(e.read())

                logger.error(msg)
                os.unlink(err.name)

                raise CryptoError(msg)
            else:
                # Cleanup err file
                err.close()
                os.unlink(err.name)

                if is_doc:
                    # Need to split twice as filename is e.g.
                    # 1-impractical_thing-doc.gz.gpg
                    fn_no_ext, _ = os.path.splitext(
                        os.path.splitext(os.path.basename(filepath))[0])
                    dest = os.path.join(self.sdc_home, "data", fn_no_ext)

                    # Docs are gzipped, so gunzip the file
                    with gzip.open(out.name, 'rb') as infile, \
                            open(dest, 'wb') as outfile:
                        shutil.copyfileobj(infile, outfile)
                else:
                    fn_no_ext, _ = os.path.splitext(target_filename)
                    dest = os.path.join(self.sdc_home, "data", fn_no_ext)
                    shutil.copy(out.name, dest)
                logger.info("Downloaded and decrypted: {}".format(dest))

                return dest
