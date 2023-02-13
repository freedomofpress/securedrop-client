"""
Helper functions for formatting information in the UI

"""
import datetime

import arrow
from dateutil import tz
from PyQt5.QtCore import QTimeZone


def format_datetime_month_day_time(date: datetime.datetime) -> str:
    """
    Formats datetime as e.g. Sep 16, 23:35
    """
    return arrow.get(date).format("MMM D, HH:mm")


def localise_datetime(date: datetime.datetime) -> datetime.datetime:
    """
    Localise the datetime object to system timezone
    """
    local_timezone = str(QTimeZone.systemTimeZoneId(), encoding="utf-8")
    return arrow.get(date).to(tz.gettz(local_timezone))

def format_datetime_local(date: datetime.datetime) -> str:
    """
    Localise date and return as a string in the format e.g. Sep 16 10:15
    """
    return format_datetime_month_day_time(localise_datetime(date))
