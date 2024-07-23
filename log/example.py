import logging

import ex1
import ex2

from securedrop_log import SecureDropLog


def main():
    handler = SecureDropLog("workvm", "logging")
    logging.basicConfig(level=logging.DEBUG, handlers=[handler])
    logger = logging.getLogger("example")

    d = ex2.Hello()
    d.talk("This should be line 1")
    ex1.fire("Where are you in middle?")
    d.talk("Oh again")
    logger.info("kushal says it works.")


if __name__ == "__main__":
    main()
