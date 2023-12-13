import logging
from securedrop_log import SecureDropLog
from systemd import journal  # type: ignore[import]
import select


def main():
    handler = SecureDropLog("workvm", "logging")
    logging.basicConfig(level=logging.DEBUG, handlers=[handler])
    logger = logging.getLogger("example")
    j = journal.Reader()
    j.seek_tail()

    p = select.poll()
    p.register(j, j.get_events())
    while True:
        p.poll()
        if j.process() == journal.APPEND:
            for m in j:
                msg = "MSG: {}".format(m["MESSAGE"])
                print(msg)
                # TODO: Figure out why the log file in the logging VM is closing
                logger.info(m["MESSAGE"])


if __name__ == "__main__":
    main()
