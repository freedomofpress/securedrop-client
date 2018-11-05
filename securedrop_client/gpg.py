from pretty_bad_protocol import GPG
from uuid import UUID

from securedrop_client.models import Source


class GpgHelper:

    def __init__(self, gpg_home: str, session) -> None:
        self.gpg_home = gpg_home
        self.gpg = GPG(homedir=self.gpg_home)
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

    def __repr__(self) -> str:
        return '<GpgHelper {}>'.format(self.gpg_home)
