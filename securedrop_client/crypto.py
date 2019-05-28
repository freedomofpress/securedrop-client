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

from sqlalchemy.orm import scoped_session
from uuid import UUID

from securedrop_client.config import Config
from securedrop_client.db import Source
from securedrop_client.utils import safe_mkdir

logger = logging.getLogger(__name__)


class CryptoError(Exception):

    pass


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

    def decrypt_submission_or_reply(self, filepath: str, target_filename: str,
                                    is_doc: bool = False) -> str:
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
            else:
                # Cleanup err file
                err.close()
                os.unlink(err.name)

                os.unlink(filepath)  # success so remove original (encrypted) file

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

    def _gpg_cmd_base(self) -> list:
        if self.is_qubes:  # pragma: no cover
            cmd = ["qubes-gpg-client"]
        else:
            cmd = ["gpg", "--homedir", os.path.join(self.sdc_home, "gpg")]

        cmd.extend(['--trust-model', 'always'])
        return cmd

    def import_key(self, source_uuid: UUID, key_data: str, fingerprint: str) -> None:
        session = self.session_maker()
        local_source = session.query(Source).filter_by(uuid=source_uuid).one()

        self._import(key_data)

        local_source.fingerprint = fingerprint
        session.add(local_source)
        session.commit()

    def _import(self, key_data: str) -> None:
        '''Wrapper for `gpg --import-keys`'''

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
