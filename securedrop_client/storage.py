"""
Functions needed to synchronise sources and submissions with the SecureDrop
server (via the securedrop_sdk). Each function requires but two arguments: an
authenticated instance of the securedrop_sdk API class, and a SQLAlchemy
session to the local database.

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
import logging
from dateutil.parser import parse
from securedrop_client.models import Source, Submission


logger = logging.getLogger(__name__)


def sync_sources(api, session):
    """
    Gets all sources from the remote server's API and ensure the local database
    session updates as follows:

    * Existing sources are updated in the local database.
    * New sources have an entry in the local database.
    * Local sources not returned by the remote server are deleted from the
      local database.
    """
    try:
        remote_sources = api.get_sources()
    except Exception as ex:
        # Log any errors but allow the caller to handle the exception.
        logger.error(ex)
        raise(ex)
    logger.info('Fetched {} remote sources.'.format(len(remote_sources)))
    local_sources = session.query(Source)
    local_uuids = {source.uuid for source in local_sources}
    for source in remote_sources:
        if source.uuid in local_uuids:
            # Update an existing record.
            existing_source = [s for s in local_sources if s.uuid==source.uuid][0]
            existing_source.journalist_designation = source.journalist_designation
            existing_source.is_flagged = source.is_flagged
            existing_source.public_key = source.key
            existing_source.interaction_count = source.interaction_count
            existing_source.is_starred = source.is_starred
            existing_source.last_updated = parse(source.last_updated)
            # Removing the UUID from local_uuids ensures this record won't be
            # deleted at the end of this function.
            local_uuids.remove(source.uuid)
            logger.info(f'Updated source {source.uuid}')
        else:
            # A new source to be added to the database.
            new_source = Source(uuid=source.uuid,
                                journalist_designation=source.journalist_designation,
                                is_flagged=source.is_flagged,
                                public_key=source.key,
                                interaction_count=source.interaction_count,
                                is_starred=source.is_starred,
                                last_updated=parse(source.last_updated))
            session.add(new_source)
            logger.info(f'Added new source {source.uuid}')
    # The uuids remaining in local_uuids do not exist on the remote server, so
    # delete the related records.
    for deleted_source in [s for s in local_sources if s.uuid in local_uuids]:
        session.delete(deleted_source)
        logger.info('Deleted source {deleted_source.uuid}')
    session.commit()


def sync_submissions(api, session):
    """
    """
    pass
