import os

import logging
logger = logging.getLogger(__name__)

# a singleton which should be instantiated with a data directory early
# in the application
class Data:
    __instance = None

    def __new__(cls, home=None):
        if Data.__instance is None and home is not None:
            Data.__instance = object.__new__(cls)
            Data.__instance.home = home
            return Data.__instance

        if Data.__instance is None and home is None: # pragma: no cover
            raise Exception('Data class must be instantiated with the home path initially!')

        if home is None:
            return Data.__instance

        logger.warning("Unusual pattern: resetting home path of Data singleton")
        Data.__instance.home = home
        return Data.__instance

    def get(self, fn):
        full_path = os.path.join(self.__instance.home, "data", fn)

        with open(full_path) as fh:
            msg = fh.read()

        return msg
