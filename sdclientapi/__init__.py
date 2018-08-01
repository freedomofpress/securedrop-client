from pprint import pprint
import json
import requests

from typing import Optional, Dict, List
from mypy_extensions import TypedDict

T_token = TypedDict("T_token", {"expiration": str, "token": str})


class BaseError(Exception):
    pass


class WrongUUIDError(BaseError):
    "For missing UUID, can be for source or submission"

    def __init__(self, message):
        self.message = message


class AuthError(BaseError):
    "For Authentication errors"

    def __init__(self, message):
        self.message = message


class AttributeError(BaseError):
    def __init__(self, message):
        self.message = message


class Submission:
    def __init__(self, **kargs) -> None:
        self.download_url = ""  # type: str
        self.filename = ""  # type: str
        self.is_read = False  # type: bool
        self.size = 0  # type: int
        self.source_url = ""  # type: str
        self.submission_url = ""  # type: str
        self.uuid = ""  # type: str

        for key in [
            "download_url",
            "filename",
            "is_read",
            "size",
            "source_url",
            "submission_url",
            "uuid",
        ]:
            if not key in kargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kargs[key])


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
        """
        Primary API class, this is the only thing which will make network call.
        """

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

    def get_source(self, uuid: str) -> Source:
        "This will return a single Source based on UUID"
        url = self.server + "api/v1/sources/{}".format(uuid)

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing source {}".format(uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return Source(**data)

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

    def get_submissions(self, source: Source) -> List[Submission]:
        url = self.server.rstrip("/") + source.submissions_url

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(source.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []  # type: List[Submission]
        values = data["submissions"]

        for val in values:
            s = Submission(**val)
            result.append(s)

        return result

    def get_submission(self, submission: Submission) -> Submission:
        url = self.server.rstrip("/") + submission.submission_url

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return Submission(**data)

    def get_all_submissions(self) -> List[Submission]:
        url = self.server.rstrip("/") + "/api/v1/submissions"

        try:
            res = requests.get(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []  # type: List[Submission]
        values = data["submissions"]

        for val in values:
            s = Submission(**val)
            result.append(s)

        return result
