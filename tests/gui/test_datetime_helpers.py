import datetime

from securedrop_client.gui.datetime_helpers import format_datetime_month_day


def test_format_datetime_month_day():
    # Dates are shown in the source list as well as the conversation view. Changing the date format may result in UI
    # issues - this test is a reminder to check both views!
    midnight_january_london = datetime.datetime(2023, 1, 1, 0, 0, 0, tzinfo=datetime.timezone.utc)

    assert format_datetime_month_day(midnight_january_london) == "Jan 1"
