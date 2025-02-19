"""
Helper functions for formatting information in the UI

"""

import datetime
import locale
from zoneinfo import ZoneInfo

from babel.dates import format_timedelta
from PyQt5.QtCore import QTimeZone


def format_datetime_month_day(date: datetime.datetime) -> str:
    """
    Formats date as e.g. Sep 16
    """
    return date.strftime("%b %-d")


def localise_datetime(date: datetime.datetime) -> datetime.datetime:
    """
    Localise the datetime object to system timezone
    """
    local_timezone = QTimeZone.systemTimeZoneId().data().decode("utf-8")
    return date.replace(tzinfo=datetime.UTC).astimezone(ZoneInfo(local_timezone))


def format_datetime_local(date: datetime.datetime) -> str:
    """
    Localise date and return as a string in the format e.g. Sep 16
    """
    return format_datetime_month_day(localise_datetime(date))


def format_relative_time(dt: datetime.datetime) -> str:
    """
    Returns a human-readable string representing the time difference
    between the given datetime and now.
    """
    now = datetime.datetime.now(datetime.UTC)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=datetime.UTC)

    lang, _ = locale.getdefaultlocale()
    if lang is None:
        # FIXME use DEFAULT_LANGUAGE (circular import)
        lang = "en"

    print(f"using locale of {lang}")

    return format_timedelta(now - dt, locale=lang)
