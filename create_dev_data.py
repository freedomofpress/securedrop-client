#!/usr/bin/env python3
import json
import os
import sys

from sqlalchemy.orm.exc import NoResultFound

from securedrop_client import db
from securedrop_client.config import Config

sdc_home = sys.argv[1]
session = db.make_session_maker(sdc_home)()
db.Base.metadata.create_all(bind=session.get_bind())

with open(os.path.join(sdc_home, Config.CONFIG_NAME), "w") as f:
    f.write(json.dumps({"journalist_key_fingerprint": "65A1B5FF195B56353CC63DFFCC40EF1228271441"}))

for download_error in db.DownloadErrorCodes:
    try:
        download_error = session.query(db.DownloadError).filter_by(name=download_error.name).one()
    except NoResultFound:
        download_error = db.DownloadError(download_error.name)
        session.add(download_error)
        session.commit()
