"""Create models with a set of default valid properties, to avoid
changes forcing an update of all test code.
"""
from datetime import datetime
from securedrop_client import models

count = 0


def Source(**attrs):
    global count
    count += 1
    defaults = dict(
        uuid='source-uuid-{}'.format(count),
        journalist_designation='testy-mctestface',
        is_flagged=False,
        public_key='mah pub key',
        interaction_count=0,
        is_starred=False,
        last_updated=datetime.now(),
        document_count=0
    )

    defaults.update(attrs)

    return models.Source(**defaults)
