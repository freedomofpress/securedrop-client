/**
 * Set the umask to restrict file permissions to owner-only access.
 *
 * This ensures that any files or directories created by the application
 * have the following permissions:
 * - Files: 0o600 (owner read/write only)
 * - Directories: 0o700 (owner read/write/execute only)
 *
 * This is in a separate file to simplify testing.
 */
export function setUmask(): void {
  process.umask(0o077);
}
