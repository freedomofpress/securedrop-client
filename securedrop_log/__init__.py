from logging import StreamHandler
from subprocess import Popen, PIPE
import threading


class Singleton(type):
    _ins = {}
    _lock = threading.Lock()

    def __call__(cls, *args, **kwargs):
        with cls._lock:  # First thread that gets here creates the instance
            if cls not in cls._ins:
                cls._ins[cls] = (super(Singleton, cls).__call__(*args, **kwargs), args)

        if len(args) > 1:
            if args != cls._ins[cls][1]:
                raise Exception("Arguments not matching for logvm name and Qubes VM name")
        return cls._ins[cls][0]


class InternalLog(metaclass=Singleton):
    def __init__(self, name, logvmname):
        self.process = Popen(
            ["/usr/lib/qubes/qrexec-client-vm", logvmname, "securedrop.Log"],
            stdin=PIPE,
            stdout=PIPE,
            stderr=PIPE,
        )
        self.write(name)

    def write(self, text):
        data = text + "\n"
        data = data.encode("utf-8")
        self.process.stdin.write(data)
        self.process.stdin.flush()


class SecureDropLog(StreamHandler):
    def __init__(self, name, logvmname):
        StreamHandler.__init__(self)
        self.qubes_log = InternalLog(name, logvmname)

    def emit(self, record):
        try:
            msg = self.format(record)
            self.qubes_log.write(msg)
            return True

        except Exception:
            self.handleError(record)
