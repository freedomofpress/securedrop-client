from logging import StreamHandler
from subprocess import Popen, PIPE


class Singleton(type):
    _ins = {}

    def __call__(cls, *args, **kwargs):
        if cls not in cls._ins:
            cls._ins[cls] = super(Singleton, cls).__call__(*args, **kwargs)

        return cls._ins[cls]


class InternalLog(metaclass=Singleton):
    def __init__(self, name, logvmname):
        self.process = Popen(
            ["/usr/lib/qubes/qrexec-client-vm", logvmname, "oqubes.Logging"],
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


class OQubesLog(StreamHandler):
    def __init__(self, name, logvmname):
        StreamHandler.__init__(self)
        self.qubes_log = InternalLog(name, logvmname)

    def emit(self, record):
        msg = self.format(record)
        self.qubes_log.write(msg)
        return True
