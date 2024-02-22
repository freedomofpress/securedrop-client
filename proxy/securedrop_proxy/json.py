"""
Wrapper around Python's json to catch duplicate keys (potential JSON injection)

This was informational finding TOB-SDW-014 in the 2020 audit.
"""

import json

dumps = json.dumps


def _check(seq):
    d = {}
    for key, value in seq:
        if key in d:
            raise ValueError(f"Key '{key}' found twice in JSON object")
        d[key] = value
    return d


def loads(text: str) -> dict:
    """
    Turn a string into a JSON object, but reject duplicate keys
    """
    return json.loads(text, object_pairs_hook=_check)
