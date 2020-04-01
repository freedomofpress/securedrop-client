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
import struct
import subprocess
import tempfile

from sqlalchemy.orm import scoped_session

from securedrop_client.config import Config
from securedrop_client.db import Source
from securedrop_client.utils import safe_mkdir

logger = logging.getLogger(__name__)


class CryptoError(Exception):

    pass


GZIP_FILE_IDENTIFICATION = b"\037\213"
GZIP_FLAG_EXTRA_FIELDS = 4  # gzip.FEXTRA
GZIP_FLAG_FILENAME = 8  # gzip.FNAME


def read_gzip_header_filename(filename: str) -> str:
    """
    Extract the original filename from the header of a gzipped file.

    Adapted from Python's gzip._GzipReader._read_gzip_header.
    """
    original_filename = ""
    with open(filename, "rb") as f:
        gzip_header_identification = f.read(2)
        if gzip_header_identification != GZIP_FILE_IDENTIFICATION:
            raise OSError("Not a gzipped file (%r)" % gzip_header_identification)

        (gzip_header_compression_method, gzip_header_flags, _) = struct.unpack("<BBIxx", f.read(8))
        if gzip_header_compression_method != 8:
            raise OSError("Unknown compression method")

        if gzip_header_flags & GZIP_FLAG_EXTRA_FIELDS:
            extra_len, = struct.unpack("<H", f.read(2))
            f.read(extra_len)

        if gzip_header_flags & GZIP_FLAG_FILENAME:
            fb = b""
            while True:
                s = f.read(1)
                if not s or s == b"\000":
                    break
                fb += s
            original_filename = str(fb, "utf-8")

    return original_filename


class GpgHelper:
    def __init__(self, sdc_home: str, session_maker: scoped_session, is_qubes: bool) -> None:
        '''
        :param sdc_home: Home directory for the SecureDrop client
        :param is_qubes: Whether the client is running in Qubes or not
        '''
        safe_mkdir(os.path.join(sdc_home), "gpg")
        self.sdc_home = sdc_home
        self.is_qubes = is_qubes
        self.session_maker = session_maker

        config = Config.from_home_dir(self.sdc_home)
        self.journalist_key_fingerprint = config.journalist_key_fingerprint

    def decrypt_submission_or_reply(self,
                                    filepath: str,
                                    plaintext_filepath: str,
                                    is_doc: bool = False) -> str:

        original_filename, _ = os.path.splitext(os.path.splitext(os.path.basename(filepath))[0])

        err = tempfile.NamedTemporaryFile(suffix=".message-error", delete=False)
        with tempfile.NamedTemporaryFile(suffix=".message") as out:
            cmd = self._gpg_cmd_base()
            cmd.extend(["--decrypt", filepath])
            res = subprocess.call(cmd, stdout=out, stderr=err)

            if res != 0:
                # The err tempfile was created with delete=False, so needs to
                # be explicitly cleaned up. We will do that after we've read the file.
                err.close()

                with open(err.name) as e:
                    msg = "GPG Error: {}".format(e.read())

                logger.error(msg)
                os.unlink(err.name)

                raise CryptoError(msg)

            # Delete err file
            err.close()
            os.unlink(err.name)

            # Delete encrypted file now that it's been successfully decrypted
            os.unlink(filepath)

            # Store the plaintext in the file located at the specified plaintext_filepath
            if is_doc:
                original_filename = read_gzip_header_filename(out.name) or plaintext_filepath
                decrypt_path = os.path.join(
                    os.path.dirname(filepath),
                    os.path.basename(original_filename)
                )
                with gzip.open(out.name, 'rb') as infile, open(decrypt_path, 'wb') as outfile:
                    shutil.copyfileobj(infile, outfile)
            else:
                shutil.copy(out.name, plaintext_filepath)

        return original_filename

    def _gpg_cmd_base(self) -> list:
        if self.is_qubes:  # pragma: no cover
            cmd = ["qubes-gpg-client"]
        else:
            cmd = ["gpg", "--homedir", os.path.join(self.sdc_home, "gpg")]

        cmd.extend(['--trust-model', 'always'])
        return cmd

    def import_key(self, source: Source) -> None:
        """
        Imports a Source's GPG key.
        """
        logger.debug("Importing key for source %s", source.uuid)
        if not source.public_key:
            raise CryptoError(f"Could not import key: source {source.uuid} has no key")
        self._import(source.public_key)

    def _import(self, key_data: str) -> None:
        """Imports a key to the client GnuPG keyring."""

        with tempfile.NamedTemporaryFile('w+') as temp_key, \
                tempfile.NamedTemporaryFile('w+') as stdout, \
                tempfile.NamedTemporaryFile('w+') as stderr:
            temp_key.write(key_data)
            temp_key.seek(0)
            if self.is_qubes:  # pragma: no cover
                cmd = ['qubes-gpg-import-key', temp_key.name]
            else:
                cmd = self._gpg_cmd_base()
                cmd.extend(['--import-options', 'import-show',
                            '--with-colons', '--import',
                            temp_key.name])

            try:
                subprocess.check_call(cmd, stdout=stdout, stderr=stderr)
            except subprocess.CalledProcessError as e:
                stderr.seek(0)
                logger.error('Could not import key: {}\n{}'.format(e, stderr.read()))
                raise CryptoError('Could not import key.')

    def encrypt_to_source(self, source_uuid: str, data: str) -> str:
        '''
        :param data: A string of data to encrypt to a source.
        '''
        session = self.session_maker()
        source = session.query(Source).filter_by(uuid=source_uuid).one()

        # do not attempt to encrypt if the journalist key is missing
        if not self.journalist_key_fingerprint:
            raise CryptoError('Could not encrypt reply due to missing fingerprint for journalist')

        # do not attempt to encrypt if the source key is missing
        if not (source.fingerprint and source.public_key):
            raise CryptoError(f'Could not encrypt reply: no key for source {source_uuid}')

        try:
            self.import_key(source)
        except CryptoError as e:
            raise CryptoError("Could not import key before encrypting reply: {e}") from e

        cmd = self._gpg_cmd_base()

        with tempfile.NamedTemporaryFile('w+') as content, \
                tempfile.NamedTemporaryFile('w+') as stdout, \
                tempfile.NamedTemporaryFile('w+') as stderr:

            content.write(data)
            content.seek(0)

            cmd.extend(['--encrypt',
                        '-r', source.fingerprint,
                        '-r', self.journalist_key_fingerprint,
                        '--armor'])
            if not self.is_qubes:
                # In Qubes, the ciphertext will go to stdout.
                # In addition the option below cannot be passed
                # through the gpg client wrapper.
                cmd.extend(['-o-'])  # write to stdout
            cmd.extend([content.name])

            try:
                subprocess.check_call(cmd, stdout=stdout, stderr=stderr)
            except subprocess.CalledProcessError as e:
                stderr.seek(0)
                logger.error(
                    'Could not encrypt to source {}: {}\n{}'.format(source_uuid, e, stderr.read()))
                raise CryptoError('Could not encrypt to source: {}.'.format(source_uuid))

            stdout.seek(0)
            return stdout.read()
