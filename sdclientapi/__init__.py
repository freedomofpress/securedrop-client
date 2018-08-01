from pprint import pprint
import json
import requests

from typing import Optional, Dict, List
from mypy_extensions import TypedDict

T_token = TypedDict("T_token", {"expiration": str, "token": str})


class BaseError(Exception):
    pass


class AuthError(BaseError):
    "For Authentication errors"

    def __init__(self, message):
        self.message = message


class AttributeError(BaseError):
    def __init__(self, message):
        self.message = message


class Source:
    def __init__(self, **kargs):
        self.add_star_url = ""  # type: str
        self.interaction_count = 0  # type: int
        self.is_flagged = False  # type: bool
        self.is_starred = False  # type: bool
        self.journalist_designation = ""  # type: str
        self.key = {}  # type: Dict
        self.last_updated = ""  # type: str
        self.number_of_documents = 0  # type: int
        self.number_of_messages = 0  # type: int
        self.remove_star_url = ""  # type: str
        self.reply_url = ""  # type: str
        self.submissions_url = ""  # type: str
        self.url = ""  # type: str
        self.uuid = ""  # type: str

        for key in [
            "add_star_url",
            "interaction_count",
            "is_flagged",
            "is_starred",
            "journalist_designation",
            "key",
            "last_updated",
            "number_of_documents",
            "number_of_messages",
            "remove_star_url",
            "reply_url",
            "submissions_url",
            "url",
            "uuid",
        ]:
            if not key in kargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kargs[key])


class API:
    def __init__(self, address, username, passphrase, totp) -> None:

        self.server = address
        self.username = username  # type: str
        self.passphrase = passphrase  # type: str
        self.totp = totp  # type: int
        self.token = {"token": "", "expiration": ""}  # type: T_token
        self.auth_header = {"Authorization": ""}  # type: Dict

    def authenticate(self) -> bool:
        user_data = {
            "username": self.username,
            "passphrase": self.passphrase,
            "one_time_code": self.totp,
        }

        token = requests.post(self.server + "api/v1/token", data=json.dumps(user_data))
        try:
            token_data = token.json()  # type: T_token
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")
        if not "expiration" in token_data:
            raise AuthError("Authentication error")
        self.token = token_data
        self.update_auth_header()

        return True

    def update_auth_header(self):
        self.auth_header = {"Authorization": "token " + self.token["token"]}

    def get_sources(self) -> List[Source]:
        url = self.server + "api/v1/sources"

        try:
            res = requests.get(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        sources = data["sources"]
        result = []  # type: List[Source]

        for source in sources:
            s = Source(**source)
            result.append(s)

        return result

    def add_star(self, source: Source) -> bool:
        url = self.server.rstrip("/") + source.add_star_url

        try:
            res = requests.post(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "message" in data and data["message"] == "Star added":
            return True

        return False

    def remove_star(self, source: Source) -> bool:
        "Removes star from a given Source"
        url = self.server.rstrip("/") + source.remove_star_url

        try:
            res = requests.delete(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "message" in data and data["message"] == "Star removed":
            return True

        return False
