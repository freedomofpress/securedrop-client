# SPDX-License-Identifier: AGPL-3.0-or-later
# Copyright © 2022 The Freedom of the Press Foundation.
import unittest
from datetime import UTC, timedelta, timezone

from securedrop_client.sdk.timestamps import parse as parse_datetime


class TestTimestamps(unittest.TestCase):
    def test_parse_invalid_date_string_returns_none(self):
        date_string = ""
        assert parse_datetime(date_string) is None

    def test_parse_iso8061_returns_appropriate_time_zone_info(self):
        date_string = "2022-02-09T07:45:26.082728+00:00"
        assert parse_datetime(date_string) is not None

        date_string = "2022-02-09T07:45:26.082728+00:00"
        dt = parse_datetime(date_string)
        assert dt.tzinfo is UTC

        date_string = "2022-02-09T07:45:26.082728+02:00"
        dt = parse_datetime(date_string)
        assert dt.tzinfo == timezone(timedelta(seconds=7200))

    def test_parse_iso8061_Z_returns_appropriate_time_zone_info(self):
        date_string = "2022-02-09T07:45:26.082728"
        assert parse_datetime(date_string) is not None

        date_string = "2022-02-09T07:45:26.082728Z"
        dt = parse_datetime(date_string)
        assert dt.tzinfo is UTC

    def test_parse_known_invalid_format_suceeds(self):
        date_string = "2022-02-09T07:45:26.082728+00:00Z"
        assert parse_datetime(date_string) is not None

        dt = parse_datetime(date_string)
        assert dt.tzinfo is UTC
