// In production, unless LOGLEVEL=debug is set, turn console.log into a no-op.
// This must be repeated for any additional workers.
export function initLogging() {
  if (
    import.meta.env.MODE === "production" &&
    process.env.LOGLEVEL !== "debug"
  ) {
    console.debug = () => {};
  }
}
