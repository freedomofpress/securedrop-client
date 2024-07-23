import datetime

from dateutil import tz
from PyQt5.QtCore import QByteArray

from securedrop_client.gui.datetime_helpers import (
    format_datetime_local,
    format_datetime_month_day,
    localise_datetime,
)


def test_format_datetime_month_day():
    # Dates are shown in the source list as well as the conversation view. Changing the date format
    # may result in UI issues - this test is a reminder to check both views!
    midnight_january_london = datetime.datetime(2023, 1, 1, 0, 0, 0, tzinfo=datetime.timezone.utc)

    assert format_datetime_month_day(midnight_january_london) == "Jan 1"


def test_localise_datetime(mocker):
    mocker.patch(
        "securedrop_client.gui.datetime_helpers.QTimeZone.systemTimeZoneId",
        return_value=QByteArray(b"Pacific/Auckland"),
    )
    evening_january_1_london = datetime.datetime(2023, 1, 1, 18, 0, 0, tzinfo=datetime.timezone.utc)
    morning_january_2_auckland = datetime.datetime(
        2023, 1, 2, 7, 0, 0, tzinfo=tz.gettz("Pacific/Auckland")
    )
    assert localise_datetime(evening_january_1_london) == morning_january_2_auckland


def test_format_datetime_local(mocker):
    mocker.patch(
        "securedrop_client.gui.datetime_helpers.QTimeZone.systemTimeZoneId",
        return_value=QByteArray(b"Pacific/Auckland"),
    )
    evening_january_1_london = datetime.datetime(2023, 1, 1, 18, 0, 0, tzinfo=datetime.timezone.utc)
    assert format_datetime_local(evening_january_1_london) == "Jan 2"
