#!/usr/bin/env python3
import json
import os
import sys
from securedrop_client.config import Config
from securedrop_client.db import Base, make_session_maker, ReplySendStatus
from securedrop_client.api_jobs.uploads import ReplySendStatusCodes

sdc_home = sys.argv[1]
session = make_session_maker(sdc_home)()
Base.metadata.create_all(bind=session.get_bind())

with open(os.path.join(sdc_home, Config.CONFIG_NAME), 'w') as f:
    f.write(json.dumps({
        'journalist_key_fingerprint': '65A1B5FF195B56353CC63DFFCC40EF1228271441',
    }))

for reply_send_status in ReplySendStatusCodes:
    reply_status = ReplySendStatus(reply_send_status.value)
    session.add(reply_status)
    session.commit()
