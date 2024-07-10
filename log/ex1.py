import logging


def fire(msg):
    logger = logging.getLogger(__name__)

    logger.debug("bye bye in debug")
