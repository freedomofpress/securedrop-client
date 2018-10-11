from pprint import pprint
import os
import json
import configparser
from subprocess import PIPE, Popen

from .sdlocalobjects import *

from typing import Optional, Dict, List, Tuple


proxyvmname = "sd-journalist"


def json_query(data):
    """
    Takes a json based query and passes to the network proxy.
    Returns the JSON output from the proxy.
    """
    global proxyvmname
    config = configparser.ConfigParser()
    try:
        if os.path.exists("/etc/sd-sdk.conf"):
            config.read("/etc/sd-sdk.conf")
            proxyvmname = config["proxy"]["name"]
    except:
        pass  # We already have a default name

    p = Popen(
        ["/usr/lib/qubes/qrexec-client-vm", proxyvmname, "securedrop.Proxy"],
        stdin=PIPE,
        stdout=PIPE,
    )
    p.stdin.write(data.encode("utf-8"))
    d = p.communicate()
    output = d[0].decode("utf-8")
    return output.strip()


class APIProxy:
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
        self.token = {"token": "", "expiration": ""}
        self.auth_header = {"Authorization": ""}  # type: Dict

    def authenticate(self, totp="") -> bool:
        """
        Authenticate the user and fetches the token from the server.

        :returns: True if authentication is successful, raise AuthError otherwise.
        """
        if not totp:
            totp = self.totp
        user_data = {
            "username": self.username,
            "passphrase": self.passphrase,
            "one_time_code": totp,
        }
        method = "POST"
        path_query = "api/v1/token"
        body = json.dumps(user_data)

        data = {"method": method, "path_query": path_query, "body": body}

        try:
            result = json.loads(json_query(json.dumps(data)))
            token_data = json.loads(result["body"])
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")
        if not "expiration" in token_data:
            raise AuthError("Authentication error")

        self.token = token_data
        self.update_auth_header()
        # If we are here, means the method call was successful.
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
        path_query = "api/v1/sources"
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}".format(source.uuid)
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}".format(source.uuid)
        method = "DELETE"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/add_star".format(source.uuid)
        method = "POST"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/remove_star".format(source.uuid)
        method = "delete"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/submissions".format(source.uuid)
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/submissions/{}".format(
            source_uuid, submission.uuid
        )
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))
            data = json.loads(res["body"])
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
        s.source_uuid = source_uuid
        s.source_url = "/api/v1/sources/{}".format(source_uuid)
        return self.get_submission(s)

    def get_all_submissions(self) -> List[Submission]:
        """
        Returns a list of Submission objects from the server.

        :returns: List of Submission objects.
        """
        path_query = "api/v1/submissions"
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/submissions/{}".format(
            source_uuid, submission.uuid
        )
        method = "DELETE"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

            data = json.loads(res["body"])
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

    def flag_source(self, source: Source) -> bool:
        """
        Flags a source for reply.

        :param source: Source object we want to flag.
        :returns: True if successful, raises Error otherwise.
        """
        path_query = "api/v1/sources/{}/flag".format(source.uuid)
        method = "POST"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return True

    def get_current_user(self):
        """
        Returns a dictionary of the current user data.

        Example:

        {
            'is_admin': True,
            'last_login': '2018-08-01T19:10:38.199429Z',
            'username': 'journalist'
        }
        """
        path_query = "api/v1/user"
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/replies".format(source.uuid)
        method = "POST"

        reply = {"reply": msg}
        body = json.dumps(reply)

        data = {
            "method": method,
            "path_query": path_query,
            "headers": self.auth_header,
            "body": body,
        }

        try:
            res = json.loads(json_query(json.dumps(data)))
            data = json.loads(res["body"])

            if res["status"] == 400:
                raise ReplyError(data["message"])

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
        path_query = "api/v1/sources/{}/replies".format(source.uuid)
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/sources/{}/replies/{}".format(source.uuid, reply_uuid)
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
            data = json.loads(res["body"])
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
        path_query = "api/v1/replies"
        method = "GET"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            data = json.loads(res["body"])
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []
        for datum in data["replies"]:
            reply = Reply(**datum)
            result.append(reply)

        return result

    def delete_reply(self, reply: Reply) -> bool:
        """
        Deletes a given Reply object from the server.

        :param reply: The Reply object we want to delete in the server.
        :returns: True if successful, raises Error otherwise.
        """
        # Not using direct URL because this helps to use the same method
        # from local reply (not fetched from server) objects.
        # See the *from_string for an example.
        source_uuid = reply.source_url.split("/")[-1]
        path_query = "api/v1/sources/{}/replies/{}".format(source_uuid, reply.uuid)
        method = "DELETE"

        data = {"method": method, "path_query": path_query, "headers": self.auth_header}

        try:
            res = json.loads(json_query(json.dumps(data)))

            if res["status"] == 404:
                raise WrongUUIDError("Missing reply {}".format(reply.uuid))

            data = json.loads(res["body"])
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Reply deleted":
            return True
        # We should never reach here
        return False
