#!/usr/bin/env python3
import os
import sys

from sqlalchemy.orm.exc import NoResultFound

from securedrop_client import db

sdc_home = sys.argv[1]
session = db.make_session_maker(sdc_home)()
db.Base.metadata.create_all(bind=session.get_bind())

os.environ["SD_SUBMISSION_KEY_FPR"] = "65A1B5FF195B56353CC63DFFCC40EF1228271441"

for reply_send_status in db.ReplySendStatusCodes:
    try:
        reply_status = (
            session.query(db.ReplySendStatus).filter_by(name=reply_send_status.value).one()
        )
    except NoResultFound:
        reply_status = db.ReplySendStatus(reply_send_status.value)
        session.add(reply_status)
        session.commit()

for download_error in db.DownloadErrorCodes:
    try:
        download_error = session.query(db.DownloadError).filter_by(name=download_error.name).one()
    except NoResultFound:
        download_error = db.DownloadError(download_error.name)
        session.add(download_error)
        session.commit()
