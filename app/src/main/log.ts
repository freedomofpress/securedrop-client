// eslint-disable-next-line @typescript-eslint/no-require-imports
const unixDgram = require("unix-dgram") as typeof import("unix-dgram");

const SYSLOG_PATH = "/dev/log";
const TAG = "securedrop-inbox";
const PID = process.pid;
const LOG_USER = 1;

const SEVERITY = { debug: 7, info: 6, warn: 4, error: 3 } as const;

type Level = keyof typeof SEVERITY;

let socket: ReturnType<(typeof unixDgram)["createSocket"]> | null = null;

function getSocket() {
  if (!socket) {
    socket = unixDgram.createSocket("unix_dgram");
    socket.on("error", () => {
      socket = null;
    });
  }
  return socket;
}

function write(level: Level, message: string): void {
  const pri = LOG_USER * 8 + SEVERITY[level];
  const buf = Buffer.from(`<${pri}>${TAG}[${PID}]: ${message}`);
  try {
    getSocket().send(buf, 0, buf.length, SYSLOG_PATH, () => {});
  } catch {
    socket = null;
  }
}

export const log = {
  debug: (message: string) => write("debug", message),
  info: (message: string) => write("info", message),
  warn: (message: string) => write("warn", message),
  error: (message: string) => write("error", message),
};
