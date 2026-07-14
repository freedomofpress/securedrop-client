import { once } from "node:events";

const mode = process.argv[2];
const argument = process.argv[3];
const etag = "sha256:legacy-proxy";

async function writeBytes(totalBytes) {
  const chunk = Buffer.alloc(64 * 1024, 0x41);
  let remaining = totalBytes;
  while (remaining > 0) {
    const length = Math.min(remaining, chunk.length);
    remaining -= length;
    if (!process.stdout.write(chunk.subarray(0, length))) {
      await once(process.stdout, "drain");
    }
  }
}

process.stdin.once("data", async () => {
  process.stdin.destroy();
  if (mode === "success") {
    await writeBytes(Number.parseInt(argument, 10));
    process.stderr.write(JSON.stringify({ headers: { etag } }));
    return;
  }
  if (mode === "empty") {
    process.stderr.write(JSON.stringify({ headers: { etag } }));
    return;
  }
  if (mode === "status") {
    const status = Number.parseInt(argument, 10);
    process.stdout.write(
      JSON.stringify({
        status,
        headers: { "content-type": "text/plain" },
        body: `legacy error ${status}`,
      }),
    );
    return;
  }
  if (mode === "oversized-error") {
    const bodyBytes = Number.parseInt(argument, 10);
    process.stdout.write(
      JSON.stringify({ status: 500, headers: {}, body: "A".repeat(bodyBytes) }),
    );
    return;
  }
  if (mode === "malformed-metadata") {
    process.stdout.write("stream body");
    process.stderr.write("{not-json");
    return;
  }
  if (mode === "oversized-metadata") {
    process.stderr.write("A".repeat(Number.parseInt(argument, 10)));
    return;
  }
  throw new Error(`Unknown legacy proxy fixture mode: ${mode}`);
});
