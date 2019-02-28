import gettext
import locale
import os


# Configure locale and language.
# Define where the translation assets are to be found.
localedir = os.path.abspath(os.path.join(os.path.dirname(__file__), 'locale'))
try:
    # Use the operating system's locale.
    current_locale, encoding = locale.getdefaultlocale()
    # Get the language code.
    language_code = current_locale[:2]
except (TypeError, ValueError):  # pragma: no cover
    language_code = 'en'  # pragma: no cover
# DEBUG/TRANSLATE: override the language code here (e.g. to Chinese).
# language_code = 'zh'
gettext.translation('securedrop_client', localedir=localedir,
                    languages=[language_code], fallback=True).install()


__version__ = '0.0.6'
