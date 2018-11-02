import os

import logging
logger = logging.getLogger(__name__)

# a singleton which should be instantiated with a data directory early
# in the application
class Data:

    def __init__(self, data_dir):
        self.data_dir = data_dir

    def get(self, fn):
        full_path = os.path.join(self.data_dir, fn)

        with open(full_path) as fh:
            msg = fh.read()

        return msg
