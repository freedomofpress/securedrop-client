#!/usr/bin/env python3
import json
import os
import sys
from securedrop_client.config import Config
from securedrop_client.db import Base, make_engine

sdc_home = sys.argv[1]
Base.metadata.create_all(make_engine(sdc_home))

with open(os.path.join(sdc_home, Config.CONFIG_NAME), 'w') as f:
    f.write(json.dumps({
        'journalist_key_fingerprint': '65A1B5FF195B56353CC63DFFCC40EF1228271441',
    }))
