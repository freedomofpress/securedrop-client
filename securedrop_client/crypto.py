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
from pretty_bad_protocol import GPG
from uuid import UUID

from securedrop_client.models import Source

logger = logging.getLogger(__name__)


class CryptoException(Exception):

    pass


class GpgHelper:

    def __init__(self, gpg_home: str, session, is_qubes: bool) -> None:
        if is_qubes:  # pragma: no cover
            gpg_binary = "qubes-gpg-client"
        else:
            gpg_binary = "gpg"
        self.gpg_home = gpg_home
        self.gpg = GPG(binary=gpg_binary, homedir=self.gpg_home)
        self.session = session

    def import_key(self, source_uuid: UUID, key_data: str) -> None:
        local_source = self.session.query(Source).filter_by(uuid=source_uuid) \
            .one_or_none()
        if local_source is None:
            raise RuntimeError('Local source not found: {}'
                               .format(source_uuid))

        res = self.gpg.import_keys(key_data)
        if not res:
            raise RuntimeError('Failed to import key.')

        # using a set because importing a private key returns two identical
        # fingerprints
        fingerprints = set(res.fingerprints)
        if len(fingerprints) != 1:
            raise RuntimeError('Expected only one fingerprint.')

        local_source.fingerprint = fingerprints.pop()
        self.session.add(local_source)
        self.session.commit()

    def encrypt_to_source(self, source_uuid: UUID, message: str) -> str:
        local_source = self.session.query(Source) \
            .filter_by(uuid=source_uuid).one()

        out = self.gpg.encrypt(message, local_source.fingerprint)
        if out.ok:
            return out.data.decode('utf-8')
        else:
            raise RuntimeError('Could not encrypt to source {!r}: {}'.format(
                source_uuid, out.stderr))

    def decrypt_submission_or_reply(self, filepath: str, target_filename: str,
                                    is_doc: bool = False):
        with tempfile.NamedTemporaryFile(suffix=".message") as output:
            res = self.gpg.decrypt_file(filepath, output=output)
            os.unlink(filepath)  # original file
            if not res:
                logger.error('Failed to decrypt message: {}'
                             .format(res.status))
                raise CryptoException()

            if is_doc:
                # Need to split twice as filename is e.g.
                # 1-impractical_thing-doc.gz.gpg
                fn_no_ext, _ = os.path.splitext(
                    os.path.splitext(os.path.basename(filepath))[0])
                dest = os.path.abspath(
                    os.path.join(self.gpg_home, "..", "data", fn_no_ext))

                # Docs are gzipped, so gunzip the file
                with gzip.open(output.name, 'rb') as infile:
                    with open(dest, 'wb') as outfile:
                        shutil.copyfileobj(infile, outfile)

            else:
                fn_no_ext, _ = os.path.splitext(target_filename)
                dest = os.path.abspath(
                    os.path.join(self.gpg_home, "..", "data", fn_no_ext))
                shutil.copy(output.name, dest)

            logger.info("Downloaded and decrypted: {}".format(dest))

        return dest

    def __repr__(self) -> str:
        return '<GpgHelper {}>'.format(self.gpg_home)
