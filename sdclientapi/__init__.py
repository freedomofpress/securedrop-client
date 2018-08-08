from pprint import pprint
import os
import json
import requests

from typing import Optional, Dict, List, Tuple
from mypy_extensions import TypedDict

T_token = TypedDict("T_token", {"expiration": str, "token": str})
T_user = TypedDict("T_user", {"is_admin": bool, "last_login": str, "username": str})


class BaseError(Exception):
    pass


class ReplyError(BaseError):
    "For errors on reply messages"

    def __init__(self, message):
        self.msg = message

    def __str__(self):
        return repr(self.msg)


class WrongUUIDError(BaseError):
    "For missing UUID, can be for source or submission"

    def __init__(self, message):
        self.msg = message

    def __str__(self):
        return repr(self.msg)


class AuthError(BaseError):
    "For Authentication errors"

    def __init__(self, message):
        self.msg = message

    def __str__(self):
        return repr(self.msg)


class AttributeError(BaseError):
    def __init__(self, message):
        self.msg = message

    def __str__(self):
        return repr(self.msg)


class Reply:
    """
    This class represents a reply to the source.
    """

    def __init__(self, **kwargs) -> None:
        self.filename = ""  # type: str
        self.journalist_username = ""  # type: str
        self.is_deleted_by_source = False  # type: bool
        self.reply_url = ""  # type: str
        self.size = 0  # type: int
        self.source_url = ""  # type: str
        self.source_uuid = ""  # type: str
        self.uuid = ""  # type: str

        for key in [
            "filename",
            "journalist_username",
            "is_deleted_by_source",
            "reply_url",
            "size",
            "source_url",
            "uuid",
        ]:
            if not key in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])

        # Now let us set source uuid
        values = self.source_url.split("/")
        self.source_uuid = values[-1]


class Submission:
    """
    This class represents a submission object in the server.
    """

    def __init__(self, **kwargs) -> None:
        self.download_url = ""  # type: str
        self.filename = ""  # type: str
        self.is_read = False  # type: bool
        self.size = 0  # type: int
        self.source_url = ""  # type: str
        self.submission_url = ""  # type: str
        self.uuid = ""  # type: str

        if ["uuid"] == list(kwargs.keys()):
            # Means we are creating an object only for fetching from server.
            self.uuid = kwargs["uuid"]
            return

        for key in [
            "download_url",
            "filename",
            "is_read",
            "size",
            "source_url",
            "submission_url",
            "uuid",
        ]:
            if not key in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])


class Source:
    """
    This class represents a source object in the server.
    """

    def __init__(self, **kwargs):
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

        if ["uuid"] == list(kwargs.keys()):
            # Means we are creating an object only for fetching from server.
            self.uuid = kwargs["uuid"]
            return

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
            if not key in kwargs:
                AttributeError("Missing key {}".format(key))
            setattr(self, key, kwargs[key])


class API:
    """
    This is class to do all the network calls to the SecureDrop API server.

    :param address: Server URL (http://localhost:8081/)
    :param username: Journalist username
    :param passphrase: Journalist passphrase
    :param totp: Current TOTP value
    :returns: An object of API class.
    """

    def __init__(self, address, username, passphrase, totp) -> None:
        """
        Primary API class, this is the only thing which will make network call.
        """

        self.server = address  # type: str
        self.username = username  # type: str
        self.passphrase = passphrase  # type: str
        self.totp = totp  # type: str
        self.token = {"token": "", "expiration": ""}  # type: T_token
        self.auth_header = {"Authorization": ""}  # type: Dict

    def authenticate(self) -> bool:
        """
        Authenticate the user and fetches the token from the server.

        :returns: True if authentication is successful, raise AuthError otherwise.
        """
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
        self.auth_header = {
            "Authorization": "token " + self.token["token"],
            "Content-Type": "application/json",
            "Accept": "application/json",
        }

    def get_sources(self) -> List[Source]:
        """
        Returns a list of all the sources from the Server.

        :returns: List of Source objects.
        """
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

    def get_source(self, source: Source) -> Source:
        """
        This will return a single Source based on UUID.

        :param source: Source object containing only source's uuid value.
        :returns: Source object fetched from server for the given UUID value.
        """
        url = self.server + "api/v1/sources/{}".format(source.uuid)

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return Source(**data)

    def get_source_from_string(self, uuid: str) -> Source:
        """
        This will fetch a source from server and return it.

        :param uuid: Source UUID as string.
        :returns: Source object fetched from server for the given UUID value.
        """

        s = Source(uuid=uuid)
        return self.get_source(s)

    def delete_source(self, source: Source) -> bool:
        """
        This method will delete the source and collection. If the uuid
        is not found in the server, it will raise WrongUUIDError.

        :param source: Source object containing only source's uuid value.
        :returns: True if successful, raises Errors in case of wrong values.
        """
        url = self.server + "api/v1/sources/{}".format(source.uuid)

        try:
            res = requests.delete(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Source and submissions deleted":
            return True

        # We should never reach here
        return False

    def delete_source_from_string(self, uuid: str) -> bool:
        """
        This method will delete the source and collection. If the uuid
        is not found in the server, it will raise WrongUUIDError.

        :param uuid: Source UUID as string.
        :returns: True if the operation is successful.
        """

        s = Source(uuid=uuid)
        return self.delete_source(s)

    def add_star(self, source: Source) -> bool:
        """
        Adds a star to a given source.

        :param source: The source object to whom we want add a star.
        :returns: True if successful, raises Error otherwise.
        """
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
        """Removes star from a given Source.

        :param source: Source object to remove the star from.
        :returns: True if successful, raises Error otherwise.
        """
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
        """
        Returns a list of Submission objects from the server for a given source.

        :param source: Source object for whom we want to find all the submissions.
        :returns: List of Submission objects.
        """
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
        """
        Returns the updated Submission object from the server.

        :param submission: Submission object we want to update.
        :returns: Updated submission object from the server.
        """
        source_uuid = submission.source_url.split("/")[-1]
        url = self.server.rstrip("/") + "/api/v1/sources/{}/submissions/{}".format(
            source_uuid, submission.uuid
        )

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

    def get_submission_from_string(self, uuid: str, source_uuid: str) -> Submission:
        """
        Returns the updated Submission object from the server.

        :param uuid: UUID of the Submission object.
        :param source_uuid: UUID of the source.
        :returns: Updated submission object from the server.
        """
        s = Submission(uuid=uuid)
        s.source_url = "/api/v1/sources/{}".format(source_uuid)
        return self.get_submission(s)

    def get_all_submissions(self) -> List[Submission]:
        """
        Returns a list of Submission objects from the server.

        :returns: List of Submission objects.
        """
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

    def delete_submission(self, submission: Submission) -> bool:
        """
        Deletes a given Submission object from the server.

        :param submission: The Submission object we want to delete in the server.
        :returns: True if successful, raises Error otherwise.
        """
        # Not using direct URL because this helps to use the same method
        # from local submission (not fetched from server) objects.
        # See the *from_string for an example.
        source_uuid = submission.source_url.split("/")[-1]
        url = self.server.rstrip("/") + "/api/v1/sources/{}/submissions/{}".format(
            source_uuid, submission.uuid
        )

        try:
            res = requests.delete(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Submission deleted":
            return True
        # We should never reach here
        return False

    def delete_submission_from_string(self, uuid: str, source_uuid: str) -> bool:
        """
        Deletes a given Submission based on uuids from the server.

        :param uuid: UUID of the Submission object.
        :param source_uuid: UUID of the source.
        :returns: Updated submission object from the server.
        """
        s = Submission(uuid=uuid)
        s.source_url = "/api/v1/sources/{}".format(source_uuid)
        return self.delete_submission(s)

    def download_submission(self, submission: Submission, path: str) -> Tuple[str, str]:
        """
        Returns a tuple of sha256sum and file path for a given Submission object. This method
        also requires a directory path in where it will save the submission file.

        :param submission: Submission object
        :param path: Local directory path to save the submission

        :returns: Tuple of sha256sum and path of the saved submission.
        """
        url = self.server.rstrip("/") + submission.download_url

        if os.path.exists(path) and not os.path.isdir(path):
            raise BaseError("Please provide a vaild directory to save.")

        try:
            res = requests.get(url, headers=self.auth_header, stream=True)

            if res.status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

            # Get the headers
            headers = res.headers
            etag = headers["Etag"]

            # This is where we will save our downloaded file
            filepath = os.path.join(path, submission.filename)
            with open(filepath, "wb") as fobj:
                for chunk in res.iter_content(
                    chunk_size=1024
                ):  # Getting 1024 in each chunk
                    if chunk:
                        fobj.write(chunk)

            # Because etag comes as JSON encoded string
            etag = json.loads(etag)
            # Return the tuple of sha256sum, filepath
            return etag[7:], filepath
        except Exception as err:
            raise BaseError(err)

    def flag_source(self, source: Source) -> bool:
        """
        Flags a source for reply.

        :param source: Source object we want to flag.
        :returns: True if successful, raises Error otherwise.
        """
        url = self.server.rstrip("/") + "/api/v1/sources/{}/flag".format(source.uuid)

        try:
            res = requests.post(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return True

    def get_current_user(self) -> T_user:
        """
        Returns a dictionary of the current user data.

        Example:

        {
            'is_admin': True,
            'last_login': '2018-08-01T19:10:38.199429Z',
            'username': 'journalist'
        }
        """
        url = self.server.rstrip("/") + "/api/v1/user"

        try:
            res = requests.get(url, headers=self.auth_header)
            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return data

    def reply_source(self, source: Source, msg: str) -> bool:
        """
        This method is used to reply to a given source. The message should be preencrypted with the source's
        GPG public key.

        :param source: Source object we want to reply.
        :param msg: Encrypted message with Source's GPG public key.
        """
        url = self.server.rstrip("/") + source.reply_url

        reply = {"reply": msg}

        try:
            res = requests.post(url, headers=self.auth_header, data=json.dumps(reply))

            if res.status_code == 400:
                raise ReplyError(res.json()["message"])

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Your reply has been stored":
            return True
        # We should never reach here
        return False

    def get_replies_from_source(self, source: Source) -> List[Reply]:
        """
        This will return a list of replies associated with a source.

        :param source: Source object containing only source's uuid value.
        :returns: List of Reply objects.
        """
        url = self.server + "api/v1/sources/{}/replies".format(source.uuid)

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []
        for datum in data["replies"]:
            reply = Reply(**datum)
            result.append(reply)

        return result

    def get_reply_from_source(self, source: Source, reply_uuid: str) -> Reply:
        """
        This will return a single specific reply.

        :param source: Source object.
        :param reply_uuid: UUID of the reply.
        :returns: A reply object
        """
        url = self.server + "api/v1/sources/{}/replies/{}".format(
            source.uuid, reply_uuid
        )

        try:
            res = requests.get(url, headers=self.auth_header)

            if res.status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        reply = Reply(**data)

        return reply

    def get_all_replies(self) -> List[Reply]:
        """
        This will return a list of all replies from the server.

        :returns: List of Reply objects.
        """
        url = self.server + "api/v1/replies"

        try:
            res = requests.get(url, headers=self.auth_header)

            data = res.json()
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []
        for datum in data["replies"]:
            reply = Reply(**datum)
            result.append(reply)

        return result
