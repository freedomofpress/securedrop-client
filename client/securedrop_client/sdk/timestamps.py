from datetime import datetime
from typing import Optional


def parse(date_string: str) -> Optional[datetime]:
    """Parse date strings in a few historical formats."""
    try:
        # ISO8061 and RFC3339
        # '2022-02-09T07:45:26.082728+00:00'
        return datetime.fromisoformat(date_string)
    except ValueError:
        try:
            # '2022-02-09T07:45:26.082728Z'
            # DEPRECATED: Please remove this once all servers were updated.
            return datetime.strptime(date_string, "%Y-%m-%dT%H:%M:%S.%f%z")
        except ValueError:
            try:
                # '2022-02-09T07:45:26.082728+00:00Z' invalid format, but we support it.
                # DEPRECATED: Please remove this once all servers were updated.
                return datetime.strptime(date_string, "%Y-%m-%dT%H:%M:%S.%f%zZ")
            except ValueError:
                return None
