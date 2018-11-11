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
import tempfile
import subprocess
from pretty_bad_protocol import GPG
from uuid import UUID

from securedrop_client.models import Source

logger = logging.getLogger(__name__)


def is_hex(s):
    try:
        int(s, 16)
        return True
    except ValueError:
        return False


class CryptoException(Exception):

    pass

class GpgHelper:

    def __init__(self, gpg_home: str, is_qubes: bool) -> None:

        self.is_qubes = is_qubes
        self.gpg_home = gpg_home

        if is_qubes:  # pragma: no cover
            self.gpg_binary = "qubes-gpg-client-wrapper"
        else:
            self.gpg_binary = "gpg"

    def _decrypt(self, source_path):
        out = tempfile.NamedTemporaryFile(suffix="sd-client-decrypt",
                                          delete=False)
        err = tempfile.NamedTemporaryFile(suffix="sd-client-decrypt-error",
                                          delete=False)

        cmd = [self.gpg_binary, "--decrypt", source_path]
        res = subprocess.call(cmd, stdout=out, stderr=err)

        os.unlink(source_path)

        if res != 0:
            out.close()
            err.close()

            with open(err.name) as e:
                msg = e.read()
                logger.error("GPG decryption error: {}".format(msg))

            os.unlink(err.name)
            os.unlink(out.name)
            raise CryptoException()

        err.close()
        os.unlink(err.name)

        out.close()
        return out.name


    def _encrypt(self, source_content, fingerprint, journalist_fingerprint):
        """
        Take some data and the fingerprint of a key, encrypt
        the data to the given key, return the name of a closed
        temporary file containing the encrypted content
        """

        content = tempfile.NamedTemporaryFile(
            suffix="sd-client-encrypt-content",
            delete=False)

        content.write(source_content.encode())
        content.close()

        out = tempfile.NamedTemporaryFile(suffix="sd-client-encrypt-out",
                                          delete=False)
        err = tempfile.NamedTemporaryFile(suffix="sd-client-encrypt-error",
                                          delete=False)

        if self.is_qubes:

            cmd = [self.gpg_binary, "--encrypt",
                   "--trust-model", "always",
                   "-r", fingerprint, "-r", journalist_fingerprint,
                   "--armor", "-o-",
                   content.name]
        else:

            cmd = [self.gpg_binary,
                   "--homedir", self.gpg_home,
                   "--trust-model", "always",
                   "--encrypt", "--armor", "-o-",
                   "-r", fingerprint,
                   content.name]

        res = subprocess.call(cmd, stdout=out, stderr=err)

        if res != 0:
            out.close()
            err.close()

            with open(err.name) as e:
                msg = e.read()
                logger.error("GPG encryption error: {}".format(msg))

            os.unlink(err.name)
            os.unlink(out.name)
            os.unlink(content.name)
            raise CryptoException()

        err.close()
        os.unlink(err.name)
        os.unlink(content.name)

        out.close()
        return out.name

    def _list_secret_keys(self):
        out = tempfile.NamedTemporaryFile(suffix="sd-client-list-keys",
                                          delete=False)
        err = tempfile.NamedTemporaryFile(suffix="sd-client-list-keys-error",
                                          delete=False)

        cmd = [self.gpg_binary, "--list-secret-keys"]

        res = subprocess.call(cmd, stdout=out, stderr=err)

        if res != 0:
            out.close()
            err.close()

            with open(err.name) as e:
                msg = e.read()
                logger.error("GPG list secret key error: {}".format(msg))

            os.unlink(err.name)
            os.unlink(out.name)
            raise CryptoException()

        err.close()
        out.close()
        os.unlink(err.name)

        with open(out.name) as o:
            cmd_res = o.read(1024)
            fingerprints = filter(lambda w: len(w) == 40 and is_hex(w),
                                  cmd_res.split())

        os.unlink(out.name)

        fingerprints = set(fingerprints)
        return fingerprints


    def _import(self, key_material: str) -> str:
        keyfile = tempfile.NamedTemporaryFile(
            mode='w',
            suffix="sd-client-pubkey-import",
            delete=False)

        keyfile.write(key_material)
        keyfile.close()

        out = tempfile.NamedTemporaryFile(suffix="sd-client-import",
                                          delete=False)
        err = tempfile.NamedTemporaryFile(suffix="sd-client-import-error",
                                          delete=False)

        if self.is_qubes:
            cmd = [self.gpg_binary, "--import", keyfile.name]
        else:
            cmd = [self.gpg_binary, "--homedir", self.gpg_home,
                   "--import", keyfile.name]

        res = subprocess.call(cmd, stdout=out, stderr=err)

        if res != 0:
            out.close()
            err.close()

            with open(err.name) as e:
                msg = e.read()
                logger.error("GPG key import error: {}".format(msg))

            os.unlink(err.name)
            os.unlink(out.name)
            raise CryptoException()

        err.close()  # in success case, output is written to STDERR
        out.close()
        os.unlink(out.name)

        with open(err.name) as o:
            cmd_res = o.read(1024)
            fingerprints = filter(lambda w: len(w) == 16 and is_hex(w),
                                  [w.strip(':') for w in cmd_res.split()])

        os.unlink(err.name)

        fingerprints = set(fingerprints)
        return fingerprints

    def import_key(self, local_source, key_data: str) -> str:

        fingerprints = self._import(key_data)

        if len(fingerprints) == 0:
            raise RuntimeError('Failed to import key.')

        if len(fingerprints) > 1:
            raise RuntimeError('Expected only one fingerprint.')

        return fingerprints.pop()

    def secret_key_fingerprint(self):
        fingerprints = self._list_secret_keys()

        if len(fingerprints) == 0:
            raise RuntimeError('Need a secret key to run at all')

        if len(fingerprints) > 1:
            raise RuntimeError('Somehow running with more than one secret key?')

        return fingerprints.pop()

    def encrypt_to_source(self, local_source,
                          journalist_key, message: str) -> str:

        out_file = self._encrypt(message,
                                 local_source.fingerprint,
                                 journalist_key)

        with open(out_file, 'r') as fh:
            encrypted = fh.read()

        os.unlink(out_file)
        return encrypted

    def decrypt_submission_or_reply(self, filepath: str,
                                    target_filename: str,
                                    is_doc: bool = False):

        decrypted_fn = self._decrypt(filepath)

        if is_doc:
            # Need to split twice as filename is e.g.
            # 1-impractical_thing-doc.gz.gpg
            fn_no_ext, _ = os.path.splitext(
                os.path.splitext(os.path.basename(filepath))[0])
            dest = os.path.abspath(
                os.path.join(self.gpg_home, "..", "data", fn_no_ext))

            # Docs are gzipped, so gunzip the file
            with gzip.open(decrypted_fn, 'rb') as infile:
                with open(dest, 'wb') as outfile:
                    shutil.copyfileobj(infile, outfile)

        else:
            fn_no_ext, _ = os.path.splitext(target_filename)
            dest = os.path.abspath(
                os.path.join(self.gpg_home, "..", "data", fn_no_ext))
            shutil.copy(decrypted_fn, dest)
            os.unlink(decrypted_fn)
        logger.info("Downloaded and decrypted: {}".format(dest))

        return dest

    def __repr__(self) -> str:
        return '<GpgHelper {}>'.format(self.gpg_home)
