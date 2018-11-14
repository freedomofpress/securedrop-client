import os

import logging
logger = logging.getLogger(__name__)


class Data:

    def __init__(self, data_dir):
        self.data_dir = data_dir

    def get(self, fn):
        full_path = os.path.join(self.data_dir, fn)

        try:
            with open(full_path) as fh:
                msg = fh.read()
        except FileNotFoundError:
            msg = "<Content deleted>"

        return msg
