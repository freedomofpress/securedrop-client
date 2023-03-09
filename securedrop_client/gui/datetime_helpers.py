"""
Helper functions for formatting information in the UI

"""
import datetime

import arrow
from dateutil import tz
from PyQt5.QtCore import QTimeZone


def format_datetime_month_day(date: datetime.datetime) -> str:
    """
    Formats date as e.g. Sep 16
    """
    return arrow.get(date).format("MMM D")


def localise_datetime(date: datetime.datetime) -> datetime.datetime:
    """
    Localise the datetime object to system timezone
    """
    local_timezone = QTimeZone.systemTimeZoneId().data().decode("utf-8")
    return arrow.get(date).to(tz.gettz(local_timezone)).datetime


def format_datetime_local(date: datetime.datetime) -> str:
    """
    Localise date and return as a string in the format e.g. Sep 16
    """
    return format_datetime_month_day(localise_datetime(date))
