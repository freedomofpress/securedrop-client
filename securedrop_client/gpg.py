from pretty_bad_protocol import GPG
from uuid import UUID

from securedrop_client.models import Source


class GpgHelper:

    def __init__(self, gpg_home: str) -> None:
        self.gpg_home = gpg_home
        self.gpg = GPG(homedir=self.gpg_home)

    def import_key(self, key_data: str) -> None:
        self.gpg.import_keys(key_data)

    def encrypt_to_source(self, source_uuid: UUID, message: str) -> str:
        local_source = self.session.query(Source) \
            .filter_by(uuid=source_uuid).one()

        out = self.gpg.encrypt(message, local_source.fingerprint)
        if out.ok:
            return out.data
        else:
            raise RuntimeError('Could not encrypt to source {!r}: {}'.format(
                source_uuid, out.stderr))
