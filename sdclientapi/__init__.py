import configparser
import json
import os
import requests
from datetime import datetime
from requests.exceptions import ConnectTimeout, ReadTimeout
from subprocess import PIPE, Popen, TimeoutExpired
from typing import List, Tuple, Dict, Optional, Any
from urllib.parse import urljoin

from .sdlocalobjects import (
    BaseError,
    WrongUUIDError,
    AuthError,
    ReplyError,
    Source,
    Reply,
    Submission,
)

DEFAULT_PROXY_VM_NAME = "sd-proxy"
DEFAULT_REQUEST_TIMEOUT = 20  # 20 seconds
DEFAULT_DOWNLOAD_TIMEOUT = 60 * 60  # 60 minutes


class RequestTimeoutError(Exception):
    """
    Error raisted if a request times out.
    """

    def __init__(self) -> None:
        super().__init__("The request timed out.")


def json_query(proxy_vm_name: str, data: str, timeout: Optional[int] = None) -> str:
    """
    Takes a json based query and passes to the network proxy.
    Returns the JSON output from the proxy.
    """
    p = Popen(
        ["/usr/lib/qubes/qrexec-client-vm", proxy_vm_name, "securedrop.Proxy"],
        stdin=PIPE,
        stdout=PIPE,
        stderr=PIPE,
    )
    p.stdin.write(data.encode("utf-8"))

    try:
        stdout, _ = p.communicate(timeout=timeout)  # type: (bytes, bytes)
    except TimeoutExpired:
        try:
            p.terminate()
        except Exception:
            pass
        raise RequestTimeoutError
    else:
        output = stdout.decode("utf-8")
        return output.strip()


class API:
    """
    This is class to do all the network calls to the SecureDrop API server.

    :param address: Server URL (http://localhost:8081/)
    :param username: Journalist username
    :param passphrase: Journalist passphrase
    :param totp: Current TOTP value
    :param proxy: Whether the API class should use the RPC proxy
    :param default_request_timeout: Default timeout for a request (non-download) in seconds
    :param default_download_timeout: Default timeout for a request (download only) in seconds
    :returns: An object of API class.
    """

    def __init__(
        self,
        address: str,
        username: str,
        passphrase: str,
        totp: str,
        proxy: bool = False,
        default_request_timeout: Optional[int] = None,
        default_download_timeout: Optional[int] = None,
    ) -> None:
        """
        Primary API class, this is the only thing which will make network call.
        """
        self.server = address
        self.username = username
        self.passphrase = passphrase
        self.totp = totp
        self.token = None  # type: Optional[str]
        self.token_expiration = None  # type: Optional[datetime]
        self.token_journalist_uuid = None  # type: Optional[str]
        self.req_headers = dict()  # type: Dict[str, str]
        self.proxy = proxy  # type: bool
        self.default_request_timeout = (
            default_request_timeout or DEFAULT_REQUEST_TIMEOUT
        )
        self.default_download_timeout = (
            default_download_timeout or DEFAULT_DOWNLOAD_TIMEOUT
        )

        self.proxy_vm_name = DEFAULT_PROXY_VM_NAME
        config = configparser.ConfigParser()
        try:
            if os.path.exists("/etc/sd-sdk.conf"):
                config.read("/etc/sd-sdk.conf")
                self.proxy_vm_name = config["proxy"]["name"]
        except Exception:
            pass  # We already have a default name

    def _send_json_request(
        self,
        method: str,
        path_query: str,
        body: Optional[str] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: Optional[int] = None,
    ) -> Tuple[Any, int, Dict[str, str]]:
        if self.proxy:  # We are using the Qubes securedrop-proxy
            func = self._send_rpc_json_request
        else:  # We are not using the Qubes securedrop-proxy
            func = self._send_http_json_request

        return func(method, path_query, body, headers, timeout)

    def _send_http_json_request(
        self,
        method: str,
        path_query: str,
        body: Optional[str] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: Optional[int] = None,
    ) -> Tuple[Any, int, Dict[str, str]]:
        url = urljoin(self.server, path_query)
        kwargs = {"headers": headers}  # type: Dict[str, Any]

        if timeout:
            kwargs["timeout"] = timeout

        if method == "POST":
            kwargs["data"] = body

        try:
            result = requests.request(method, url, **kwargs)
        except (ConnectTimeout, ReadTimeout):
            raise RequestTimeoutError

        # Because when we download a file there is no JSON in the body
        if path_query.endswith("/download"):
            return result, result.status_code, dict(result.headers)

        return result.json(), result.status_code, dict(result.headers)

    def _send_rpc_json_request(
        self,
        method: str,
        path_query: str,
        body: Optional[str] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: Optional[int] = None,
    ) -> Tuple[Any, int, Dict[str, str]]:
        data = {"method": method, "path_query": path_query}  # type: Dict[str, Any]

        if method == "POST":
            data["body"] = body

        if headers is not None and headers:
            data["headers"] = headers

        data_str = json.dumps(data)
        result = json.loads(json_query(self.proxy_vm_name, data_str, timeout))
        return json.loads(result["body"]), result["status"], result["headers"]

    def authenticate(self, totp: Optional[str] = None) -> bool:
        """
        Authenticate the user and fetches the token from the server.

        :returns: True if authentication is successful, raise AuthError otherwise.
        """
        if totp is None:
            totp = self.totp

        user_data = {
            "username": self.username,
            "passphrase": self.passphrase,
            "one_time_code": totp,
        }

        method = "POST"
        path_query = "api/v1/token"
        body = json.dumps(user_data)

        try:
            token_data, status_code, headers = self._send_json_request(
                method, path_query, body=body, timeout=self.default_request_timeout
            )
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "expiration" not in token_data:
            raise AuthError("Authentication error")

        self.token = token_data["token"]
        self.token_expiration = datetime.strptime(
            token_data["expiration"], "%Y-%m-%dT%H:%M:%S.%fZ"
        )
        self.token_journalist_uuid = token_data["journalist_uuid"]

        self.update_auth_header()

        return True

    def update_auth_header(self) -> None:
        if self.token is not None:
            self.req_headers = {
                "Authorization": "Token " + self.token,
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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )
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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )
            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
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
        method = "DELETE"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )
            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))
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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(source.uuid))

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
        path_query = "api/v1/sources/{}/submissions/{}".format(
            submission.source_uuid, submission.uuid
        )
        method = "GET"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

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
        return self.get_submission(s)

    def get_all_submissions(self) -> List[Submission]:
        """
        Returns a list of Submission objects from the server.

        :returns: List of Submission objects.
        """
        path_query = "api/v1/submissions"
        method = "GET"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )
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
        path_query = "api/v1/sources/{}/submissions/{}".format(
            submission.source_uuid, submission.uuid
        )
        method = "DELETE"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

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

    def download_submission(
        self, submission: Submission, path: str = "", timeout: Optional[int] = None
    ) -> Tuple[str, str]:
        """
        Returns a tuple of sha256sum and file path for a given Submission object. This method
        also requires a directory path in where it will save the submission file.

        :param submission: Submission object
        :param path: Local directory path to save the submission

        :returns: Tuple of sha256sum and path of the saved submission.
        """
        path_query = "api/v1/sources/{}/submissions/{}/download".format(
            submission.source_uuid, submission.uuid
        )
        method = "GET"

        if path:
            if os.path.exists(path) and not os.path.isdir(path):
                raise BaseError("Please provide a vaild directory to save.")

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=timeout or self.default_download_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing submission {}".format(submission.uuid))

            # Get the headers
            headers = headers

            if not self.proxy:
                # This is where we will save our downloaded file
                filepath = os.path.join(path, submission.filename)
                with open(filepath, "wb") as fobj:
                    for chunk in data.iter_content(
                        chunk_size=1024
                    ):  # Getting 1024 in each chunk
                        if chunk:
                            fobj.write(chunk)

            else:
                filepath = os.path.join(
                    "/home/user/QubesIncoming/", self.proxy_vm_name, data["filename"]
                )
            # Return the tuple of sha256sum, filepath
            # Returning empty string instead of sha256sum due to this
            # SecureDrop server bug:
            # https://github.com/freedomofpress/securedrop/issues/3877
            return "", filepath
        except Exception as err:
            raise BaseError(err)

    def flag_source(self, source: Source) -> bool:
        """
        Flags a source for reply.

        :param source: Source object we want to flag.
        :returns: True if successful, raises Error otherwise.
        """
        path_query = "api/v1/sources/{}/flag".format(source.uuid)
        method = "POST"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return True

    def get_current_user(self) -> Any:
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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        return data

    def reply_source(
        self, source: Source, msg: str, reply_uuid: Optional[str] = None
    ) -> Reply:
        """
        This method is used to reply to a given source. The message should be preencrypted with the
        source's GPG public key.

        :param source: Source object we want to reply.
        :param msg: Encrypted message with Source's GPG public key.
        :param reply_uuid: The UUID that will be used to identify the reply on the server.
        """
        path_query = "api/v1/sources/{}/replies".format(source.uuid)
        method = "POST"
        reply = {"reply": msg}

        if reply_uuid:
            reply["uuid"] = reply_uuid

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                body=json.dumps(reply),
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 400:
                raise ReplyError(data["message"])

        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Your reply has been stored":
            return Reply(uuid=data["uuid"], filename=data["filename"])

        raise BaseError("Error handling HTTP response to sending a reply")

    def get_replies_from_source(self, source: Source) -> List[Reply]:
        """
        This will return a list of replies associated with a source.

        :param source: Source object containing only source's uuid value.
        :returns: List of Reply objects.
        """
        path_query = "api/v1/sources/{}/replies".format(source.uuid)
        method = "GET"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing source {}".format(source.uuid))

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

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        result = []
        for datum in data["replies"]:
            reply = Reply(**datum)
            result.append(reply)

        return result

    def download_reply(self, reply: Reply, path: str = "") -> Tuple[str, str]:
        """
        Returns a tuple of sha256sum and file path for a given Reply object. This method
        also requires a directory path in where it will save the reply file.

        :param reply: Reply object
        :param path: Local directory path to save the reply

        :returns: Tuple of sha256sum and path of the saved Reply.
        """
        path_query = "api/v1/sources/{}/replies/{}/download".format(
            reply.source_uuid, reply.uuid
        )

        method = "GET"

        if path:
            if os.path.exists(path) and not os.path.isdir(path):
                raise BaseError("Please provide a valid directory to save.")

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing reply {}".format(reply.uuid))

            # Get the headers
            headers = headers

            if not self.proxy:
                # This is where we will save our downloaded file
                filepath = os.path.join(path, reply.filename)
                with open(filepath, "wb") as fobj:
                    for chunk in data.iter_content(
                        chunk_size=1024
                    ):  # Getting 1024 in each chunk
                        if chunk:
                            fobj.write(chunk)

            else:
                filepath = os.path.join(
                    "/home/user/QubesIncoming/", self.proxy_vm_name, data["filename"]
                )
            # Return the tuple of sha256sum, filepath
            # Returning empty string instead of sha256sum due to this
            # SecureDrop server bug:
            # https://github.com/freedomofpress/securedrop/issues/3877
            return "", filepath
        except Exception as err:
            raise BaseError(err)

    def delete_reply(self, reply: Reply) -> bool:
        """
        Deletes a given Reply object from the server.

        :param reply: The Reply object we want to delete in the server.
        :returns: True if successful, raises Error otherwise.
        """
        # Not using direct URL because this helps to use the same method
        # from local reply (not fetched from server) objects.
        # See the *from_string for an example.
        path_query = "api/v1/sources/{}/replies/{}".format(
            reply.source_uuid, reply.uuid
        )

        method = "DELETE"

        try:
            data, status_code, headers = self._send_json_request(
                method,
                path_query,
                headers=self.req_headers,
                timeout=self.default_request_timeout,
            )

            if status_code == 404:
                raise WrongUUIDError("Missing reply {}".format(reply.uuid))
        except json.decoder.JSONDecodeError:
            raise BaseError("Error in parsing JSON")

        if "error" in data:
            raise AuthError(data["error"])

        if "message" in data and data["message"] == "Reply deleted":
            return True
        # We should never reach here
        return False
