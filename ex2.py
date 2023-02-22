import logging


class Hello:
    def __init__(self, *args, **kwargs):
        self.logger = logging.getLogger(__name__)

    def talk(self, msg):
        self.logger.debug(msg)
