"""
Helper functions for formatting information in the UI

"""

import datetime

import arrow
from dateutil import tz
from PyQt5.QtCore import QTimeZone


def format_datetime_month_day(date: datetime.datetime, long_format: bool = False) -> str:
    """
    Formats date: "h:MM" if in the current day, "Mon DD" if
    current year, Mon DD YYYY if not current year
    """
    if long_format:
        return arrow.get(date).format("MMM D YYYY, h:mm A")

    today = datetime.date.today()
    if date.date() == today:
        return arrow.get(date).format("h:mm A")
    elif date.date().year == today.year:
        return arrow.get(date).format("MMM D")
    else:
        return arrow.get(date).format("MMM D, YYYY")


def localise_datetime(date: datetime.datetime) -> datetime.datetime:
    """
    Localise the datetime object to system timezone
    """
    local_timezone = QTimeZone.systemTimeZoneId().data().decode("utf-8")
    return arrow.get(date).to(tz.gettz(local_timezone)).datetime


def format_datetime_local(date: datetime.datetime, long_format: bool = False) -> str:
    """
    Localise date and return as a string in the format e.g. Sep 16
    """
    return format_datetime_month_day(localise_datetime(date), long_format)
