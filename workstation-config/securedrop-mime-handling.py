#!/usr/bin/python3
##
# securedrop-mime-handling
# =====================
#
# Overrides mimetype handling for certain VMs. Instead of relying on the
# /usr/share/applications (system volume), we instead use /home/user/.local/share/
# to be provisioned on boot by systemd.
##

import logging
import logging.handlers
import sys
from pathlib import Path

from qubesdb import QubesDB

# Configure logging
syslog_handler = logging.handlers.SysLogHandler(address="/dev/log")

stdout_handler = logging.StreamHandler(sys.stdout)
logging.basicConfig(level=logging.INFO, handlers=[syslog_handler, stdout_handler])
logger = logging.getLogger()


def create_symlink_strict(source_path_str, target_path_str, overwrite_expected=False):
    """
    Creates a symlink, but warning when idempotence is required and failing if
    link source already exsits.
    """
    source_path = Path(source_path_str)
    target_path = Path(target_path_str)
    target_path.resolve(strict=True)  # raise exception if does not exist

    try:
        source_path.symlink_to(target_path)
    except FileExistsError as e:
        if source_path.is_symlink():
            if source_path.readlink() == target_path:
                if not overwrite_expected:
                    # Harmless situation, yet not ideal (idempotency required)
                    logger.warning(f"'{source_path}' existed already (unexpected)")
            else:
                logger.error(f"'{source_path}' existed already and is linked to the wrong file")
                raise e
        else:
            logger.error(f"'{source_path}' existed already")
            raise e


def get_mime_handling():
    mime_handling = QubesDB().read("/vm-config/SD_MIME_HANDLING")
    if mime_handling is None or len(mime_handling) == 0:
        raise RuntimeError("'SD_MIME_HANDLING' qubesdb vm-config is not set")
    return mime_handling.decode()


def main():
    # Should fail on DVM templates to avoid tainting the disposables' home.
    # In practice we cannot detect this from within, so we have to hard-code
    # sd-app as the only valid non-disposable.
    persistent_home = QubesDB().read("/qubes-vm-persistence").decode() != "none"
    vm_name = QubesDB().read("/name").decode()
    if persistent_home and vm_name != "sd-app":
        sys.exit(1)

    # Ensure applications open with the correct tool (or disposable qube)
    mime_handling = get_mime_handling()
    mimeapps_override_path = Path(f"/opt/sdw/mimeapps.list.{mime_handling}")
    mimeapps_override_path.resolve(strict=True)
    user_apps_dir_path = Path("/home/user/.local/share/applications")
    user_apps_dir_path.mkdir(mode=0o755, parents=True, exist_ok=True)
    create_symlink_strict(
        user_apps_dir_path / "mimeapps.list",
        mimeapps_override_path,
        overwrite_expected=persistent_home,
    )

    # Fallback mechanism if MIME type lookup fails in tools like xdg-open
    create_symlink_strict(
        "/home/user/.mailcap", "/opt/sdw/mailcap.default", overwrite_expected=persistent_home
    )


if __name__ == "__main__":
    main()
