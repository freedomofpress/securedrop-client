import configparser
import http
import json
import logging
import os
import subprocess
import tempfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

from securedrop_client import utils
from securedrop_client.config import Config

from .sdlocalobjects import (
    AuthError,
    BaseError,
    Reply,
    ReplyError,
    Source,
    Submission,
    User,
    WrongUUIDError,
)
from .timestamps import parse as parse_datetime

logger = logging.getLogger(__name__)

DEFAULT_PROXY_VM_NAME = "sd-proxy"
DEFAULT_REQUEST_TIMEOUT = 20  # 20 seconds
DEFAULT_DOWNLOAD_TIMEOUT = 60 * 60  # 60 minutes


class RequestTimeoutError(Exception):
    """
    Error raised if a request times out.
    """

    def __init__(self) -> None:
        super().__init__("The request timed out.")

    def __reduce__(self) -> tuple[type, tuple]:
        return (self.__class__, ())


class ServerConnectionError(Exception):
    """
    Error raised if we cannot connect to the server.
    """

    def __init__(self) -> None:
        super().__init__("Cannot connect to the server.")

    def __reduce__(self) -> tuple[type, tuple]:
        return (self.__class__, ())


@dataclass(frozen=True)
class StreamedResponse:
    """Container for streamed data along with the ETag checksum sent by the server."""

    contents: bytes
    sha256sum: str


@dataclass(frozen=True)
class JSONResponse:
    """Deserialization of the proxy's `OutgoingResponse`."""

    data: dict
    status: int
    headers: dict[str, str]


class API:
    """
    This class handles all network calls to the SecureDrop API server.

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
        default_request_timeout: int | None = None,
        default_download_timeout: int | None = None,
    ) -> None:
        """
        Primary API class, this is the only thing which will make network call.
        """
        self.server = address
        self.username = username
        self.passphrase = passphrase
        self.totp = totp
        self.token: str | None = None
        self.token_expiration: datetime | None = None
        self.token_journalist_uuid: str | None = None
        self.first_name: str | None = None
        self.last_name: str | None = None
        self.development_mode: bool = not proxy
        self.default_request_timeout = default_request_timeout or DEFAULT_REQUEST_TIMEOUT
        self.default_download_timeout = default_download_timeout or DEFAULT_DOWNLOAD_TIMEOUT

        self.proxy_vm_name = DEFAULT_PROXY_VM_NAME
        config_parser = configparser.ConfigParser()
        try:
            if os.path.exists("/etc/sd-sdk.conf"):
                config_parser.read("/etc/sd-sdk.conf")
                self.proxy_vm_name = config_parser["proxy"]["name"]
        except Exception:
            pass  # We already have a default name

        # Load download retry limit from the config
        self.download_retry_limit = Config.load().download_retry_limit

    def _rpc_target(self) -> list:
        """In `development_mode`, check `cargo` for a locally-built proxy binary.
        Otherwise, call `securedrop.Proxy` via qrexec."""
        if not self.development_mode:
            return ["/usr/lib/qubes/qrexec-client-vm", self.proxy_vm_name, "securedrop.Proxy"]
        # Development mode, find the target directory and look for a debug securedrop-proxy
        # binary. We assume that `cargo build` has already been run. We don't use `cargo run`
        # because it adds its own output that would interfere with ours.
        target_directory = json.loads(
            subprocess.check_output(["cargo", "metadata", "--format-version", "1"], text=True)
        )["target_directory"]
        return [f"{target_directory}/debug/securedrop-proxy"]

    def _streaming_download(
        self, data: dict[str, Any], env: dict
    ) -> StreamedResponse | JSONResponse:
        fobj = tempfile.TemporaryFile("w+b")

        retry = 0
        bytes_written = 0
        download_finished = False

        while not download_finished and retry < self.download_retry_limit:
            logger.debug(f"Streaming download, retry {retry}")

            try:
                # Update the range request if we're retrying
                if retry > 0:
                    data["headers"]["Range"] = f"bytes={bytes_written}-"
                    logger.debug(f"Retry {retry}, range: {bytes_written}-")

                # Serialize the data to send
                data_bytes = json.dumps(data).encode()

                # Open the process
                logger.debug(f"Retry {retry}, opening process")
                proc = subprocess.Popen(
                    self._rpc_target(),
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    env=env,
                )

                # Send the input data
                if proc.stdin is not None:
                    logger.debug(f"Retry {retry}, sending data")
                    proc.stdin.write(data_bytes)
                    proc.stdin.close()
                else:
                    logger.error(f"Retry {retry}, stdin is None")
                    # TODO: should we raise an exception here? If we don't pass in stdin,
                    # the request will end up failing

                # Write the contents to disk
                chunk_size = 1024
                while not download_finished:
                    if proc.stdout is not None:
                        chunk = proc.stdout.read(chunk_size)
                        if not chunk:
                            logger.debug(f"Retry {retry}, download finished")
                            download_finished = True
                            break

                    fobj.write(chunk)
                    bytes_written += len(chunk)
                    logger.debug(f"Retry {retry}, bytes written: {bytes_written:,}")

                # Wait for the process to end
                returncode = proc.wait()
                logger.debug(f"Retry {retry}, process ended with return code {returncode}")

                # Check for errors
                if returncode != 0:
                    # Actually, the download did not finish after all
                    download_finished = False

                    error = {}
                    if proc.stderr is not None:
                        error_json = proc.stderr.read().decode()
                        try:
                            error = json.loads(error_json)
                        except json.decoder.JSONDecodeError as err:
                            logger.debug(f"Retry {retry}, invalid error JSON: {error_json}")
                            raise BaseError("Unable to parse stderr JSON") from err
                    error_description = error.get("error", "unknown error")
                    logger.debug(f"Retry {retry}, internal proxy error: {error_description}")
                    logger.error(f"Retry {retry}, internal proxy error")
                    raise BaseError(f"Internal proxy error: {error_description}")

                # FIXME: For now, store the contents as bytes
                logger.debug(f"Retry {retry}, reading contents from disk")
                fobj.seek(0)
                contents = fobj.read()
                fobj.close()

                # Check for an error response
                if contents[0:1] == b"{":
                    logger.error(f"Retry {retry}, received JSON error response.")
                    return self._handle_json_response(contents)

                # Get the headers
                if proc.stderr is not None:
                    headers_json = proc.stderr.read().decode()
                    try:
                        stderr = json.loads(headers_json)
                    except json.decoder.JSONDecodeError as err:
                        logger.debug(
                            f"Retry {retry}, invalid headers (stderr) JSON: {headers_json}"
                        )
                        raise BaseError("Unable to parse headers (stderr) JSON") from err

                    sha256sum = stderr["headers"]["etag"]
                else:
                    # This should never happen because we should always have an stderr
                    sha256sum = ""

                return StreamedResponse(
                    contents=contents,
                    sha256sum=sha256sum,
                )

            except subprocess.TimeoutExpired as err:
                logger.error(f"Retry {retry}, timeout expired")
                retry += 1
                if retry >= self.download_retry_limit:
                    logger.error("Retry limit reached after subprocess.TimeoutExpired")
                    raise RequestTimeoutError from err
            except BaseError as err:
                logger.debug(f"Retry {retry}, base error: {err}")
                logger.error(f"Retry {retry}, base error")
                retry += 1
                if retry >= self.download_retry_limit:
                    logger.error("Retry limit reached after BaseError")
                    raise err

        # We will never reach this code because we'll have already returned or raised
        # an exception by now, but it's required to make the linter happy
        logger.error(
            f"Reached unreachable exception. retry={retry}, "
            f"bytes_written={bytes_written}, download_finished={download_finished}"
        )
        raise RuntimeError(
            "This should be unreachable, we should've already returned or raised a different exception"  # noqa: E501
        )

    def _handle_json_response(self, stdout_bytes: bytes) -> JSONResponse:
        try:
            result = json.loads(stdout_bytes.decode())
        except json.decoder.JSONDecodeError as err:
            raise BaseError("Unable to parse stdout JSON") from err

        if result["status"] == http.HTTPStatus.GATEWAY_TIMEOUT:
            raise RequestTimeoutError
        elif result["status"] == http.HTTPStatus.BAD_GATEWAY:
            raise ServerConnectionError
        elif result["status"] == http.HTTPStatus.FORBIDDEN:
            raise AuthError("Forbidden")
        elif result["status"] == http.HTTPStatus.BAD_REQUEST:
            # FIXME: return a more generic error
            raise ReplyError("bad request")
        elif (
            str(result["status"]).startswith(("4", "5"))
            and result["status"] != http.HTTPStatus.NOT_FOUND
        ):
            # We exclude 404 since if we encounter a 404, it means that an
            # item is missing. In that case we return to the caller to
            # handle that with an appropriate message. However, if the error
            # is not a 404, then we raise.
            logger.error(f"API error: status={result['status']}")
            raise BaseError(f"Unknown error, status: {result['status']}")

        data = json.loads(result["body"])
        return JSONResponse(data=data, status=result["status"], headers=result["headers"])

    def _send_json_request(
        self,
        method: str,
        path_query: str,
        stream: bool = False,
        body: str | None = None,
        headers: dict[str, str] | None = None,
        timeout: int | None = None,
    ) -> StreamedResponse | JSONResponse:
        """Build a JSON-serialized request to pass to the proxy.
        Handle the JSON or streamed response back, plus translate HTTP error statuses
        to our exceptions."""

        data: dict[str, Any] = {"method": method, "path_query": path_query, "stream": stream}

        if method == "POST" and body:
            data["body"] = body

        if headers:
            data["headers"] = headers

        if timeout:
            data["timeout"] = timeout

        logger.debug(
            f"Sending request to proxy: {method} {path_query} (body={'body' in data}, "
            f"stream={stream}, timeout={timeout})"
        )

        env = {}
        if self.development_mode:
            env["SD_PROXY_ORIGIN"] = self.server

        # Streaming
        if stream:
            return self._streaming_download(data, env)

        # Not streaming
        data_str = json.dumps(data).encode()
        try:
            response = subprocess.run(
                self._rpc_target(),
                capture_output=True,
                timeout=timeout,
                input=data_str,
                env=env,
                check=False,
            )
        except subprocess.TimeoutExpired as err:
            logger.error(f"Non-streaming reqest timed out (path_query={path_query})")
            raise RequestTimeoutError from err

        # Error handling
        if response.returncode != 0:
            error_json = response.stderr.decode()
            try:
                error = json.loads(error_json)
            except json.decoder.JSONDecodeError as err:
                logger.debug(f"Unable to parse stderr JSON: {error_json}")
                raise BaseError("Unable to parse stderr JSON") from err
            error_desc = error.get("error", "unknown error")
            logger.debug(f"Internal proxy error: {error_desc}")
            logger.error("Internal proxy error (non-streaming)")
            raise BaseError(f"Internal proxy error: {error_desc}")

        return self._handle_json_response(response.stdout)

    def authenticate(self, totp: str | None = None) -> bool:
        """
        Authenticates the user and fetches the token from the server.

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

        response = self._send_json_request(
            method, path_query, body=body, timeout=self.default_request_timeout
        )
        assert isinstance(response, JSONResponse)

        if "expiration" not in response.data:
            raise AuthError("Authentication error")

        token_expiration = parse_datetime(response.data["expiration"])
        if token_expiration is None:
            raise BaseError("Error in parsing token expiration time")

        self.token = response.data["token"]
        self.token_expiration = token_expiration
        self.token_journalist_uuid = response.data["journalist_uuid"]
        self.first_name = response.data["journalist_first_name"]
        self.last_name = response.data["journalist_last_name"]

        return True

    def build_headers(self) -> dict[str, str]:
        # Build headers dynamically each time to make sure
        # the dict is safe to mutate.
        headers = {
            "Content-Type": "application/json",
            "Accept": "application/json",
        }

        if self.token is not None:
            headers["Authorization"] = "Token " + self.token

        return headers

    def get_sources(self) -> list[Source]:
        """
        Returns a list of all the sources from the Server.

        :returns: List of Source objects.
        """
        path_query = "api/v1/sources"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        sources = response.data["sources"]
        result: list[Source] = []

        for source in sources:
            s = Source(**source)
            result.append(s)

        return result

    def get_source(self, source: Source) -> Source:
        """
        This will return a single Source based on UUID.

        :param source: Source object containing only source's UUID value.
        :returns: Source object fetched from server for the given UUID value.
        """
        path_query = f"api/v1/sources/{source.uuid}"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        return Source(**response.data)

    def delete_source(self, source: Source) -> bool:
        """
        This method will delete the source and collection. If the UUID
        is not found in the server, it will raise WrongUUIDError.

        :param source: Source object containing only source's UUID value.
        :returns: True if successful, raises Errors in case of wrong values.
        """
        path_query = f"api/v1/sources/{source.uuid}"
        method = "DELETE"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        if response.data.get("message") == "Source and submissions deleted":
            return True

        # We should never reach here
        return False

    def delete_conversation(self, uuid: str) -> bool:
        """
        This method will delete the source's conversation.

        If the UUID is not found in the server, it will raise WrongUUIDError.

        :param uuid: Source UUID as string.
        :returns: True if the operation is successful.
        """

        path_query = f"api/v1/sources/{uuid}/conversation"
        method = "DELETE"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {uuid}")

        if response.data.get("message") == "Source data deleted":
            return True

        return False

    def add_star(self, source: Source) -> bool:
        """
        Adds a star to a given source.

        :param source: The source object to whom we want add a star.
        :returns: True if successful, raises Error otherwise.
        """
        path_query = f"api/v1/sources/{source.uuid}/add_star"
        method = "POST"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        if response.data.get("message") == "Star added":
            return True

        return False

    def remove_star(self, source: Source) -> bool:
        """Removes star from a given Source.

        :param source: Source object to remove the star from.
        :returns: True if successful, raises Error otherwise.
        """
        path_query = f"api/v1/sources/{source.uuid}/remove_star"
        method = "DELETE"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        if response.data.get("message") == "Star removed":
            return True

        return False

    def get_submissions(self, source: Source) -> list[Submission]:
        """
        Returns a list of Submission objects from the server for a given source.

        :param source: Source object for whom we want to find all the submissions.
        :returns: List of Submission objects.
        """
        path_query = f"api/v1/sources/{source.uuid}/submissions"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing submission {source.uuid}")

        result: list[Submission] = []
        values = response.data["submissions"]

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
        if submission.source_uuid and submission.uuid is not None:
            path_query = f"api/v1/sources/{submission.source_uuid}/submissions/{submission.uuid}"
            method = "GET"

            response = self._send_json_request(
                method,
                path_query,
                headers=self.build_headers(),
                timeout=self.default_request_timeout,
            )
            assert isinstance(response, JSONResponse)

            if response.status == 404:
                raise WrongUUIDError(f"Missing submission {submission.uuid}")

            return Submission(**response.data)
        else:
            # XXX: is this the correct behavior
            return submission

    def get_all_submissions(self) -> list[Submission]:
        """
        Returns a list of Submission objects from the server.

        :returns: List of Submission objects.
        """
        path_query = "api/v1/submissions"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        result: list[Submission] = []
        values = response.data["submissions"]

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
        path_query = f"api/v1/sources/{submission.source_uuid}/submissions/{submission.uuid}"
        method = "DELETE"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing submission {submission.uuid}")

        if response.data.get("message") == "Submission deleted":
            return True
        # We should never reach here
        return False

    def download_submission(
        self, submission: Submission, original_path: str | None = None, timeout: int | None = None
    ) -> tuple[str, str]:
        """
        Returns a tuple of etag (format is algorithm:checksum) and file path for
        a given Submission object. This method requires a directory path
        at which to save the submission file.

        :param submission: Submission object
        :param original_path: Local directory path to save the submission, if None, use ~/Downloads

        :returns: Tuple of etag and path of the saved submission.
        """
        path_query = (
            f"api/v1/sources/{submission.source_uuid}/submissions/{submission.uuid}/download"
        )
        method = "GET"

        if original_path:
            path = Path(original_path)
        else:
            path = Path("~/Downloads").expanduser()

        if not path.is_dir():
            raise BaseError(f"Specified path isn't a directory: {path}")

        response = self._send_json_request(
            method,
            path_query,
            stream=True,
            headers=self.build_headers(),
            timeout=timeout or self.default_download_timeout,
        )

        if isinstance(response, JSONResponse):
            if response.status == 404:
                raise WrongUUIDError(f"Missing submission {submission.uuid}")
            else:
                raise BaseError(f"Unknown error, status code: {response.status}")

        filepath = path / submission.filename
        # submission.filename should have already been validated, but let's
        # double check before we write anything
        utils.check_path_traversal(filepath)
        filepath.write_bytes(response.contents)

        return response.sha256sum.strip('"'), str(filepath)

    def flag_source(self, source: Source) -> bool:
        """
        Flags a source for reply.

        :param source: Source object we want to flag.
        :returns: True if successful, raises Error otherwise.
        """
        path_query = f"api/v1/sources/{source.uuid}/flag"
        method = "POST"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        return True

    def get_current_user(self) -> dict:
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

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        return response.data

    def get_users(self) -> list[User]:
        """
        Returns a list of all the journalist and admin users registered on the
        server.

        :returns: List of User objects.
        """
        path_query = "api/v1/users"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        users = response.data["users"]
        result: list[User] = []

        for user in users:
            u = User(**user)
            result.append(u)

        return result

    def reply_source(self, source: Source, msg: str, reply_uuid: str | None = None) -> Reply:
        """
        This method is used to reply to a given source. The message should be preencrypted with the
        source's GPG public key.

        :param source: Source object to whom we want to reply.
        :param msg: Encrypted message with Source's GPG public key.
        :param reply_uuid: The UUID that will be used to identify the reply on the server.
        """
        path_query = f"api/v1/sources/{source.uuid}/replies"
        method = "POST"
        reply = {"reply": msg}

        if reply_uuid:
            reply["uuid"] = reply_uuid

        response = self._send_json_request(
            method,
            path_query,
            body=json.dumps(reply),
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.data.get("message") == "Your reply has been stored":
            return Reply(uuid=response.data["uuid"], filename=response.data["filename"])

        raise ReplyError("bad request")

    def get_replies_from_source(self, source: Source) -> list[Reply]:
        """
        This will return a list of replies associated with a source.

        :param source: Source object containing only source's UUID value.
        :returns: List of Reply objects.
        """
        path_query = f"api/v1/sources/{source.uuid}/replies"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing source {source.uuid}")

        result = []
        for datum in response.data["replies"]:
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
        if source.uuid and reply_uuid is not None:
            path_query = f"api/v1/sources/{source.uuid}/replies/{reply_uuid}"
            method = "GET"

            response = self._send_json_request(
                method,
                path_query,
                headers=self.build_headers(),
                timeout=self.default_request_timeout,
            )
            assert isinstance(response, JSONResponse)

            if response.status == 404:
                raise WrongUUIDError(f"Missing source {source.uuid}")

            reply = Reply(**response.data)

        return reply

    def get_all_replies(self) -> list[Reply]:
        """
        This will return a list of all replies from the server.

        :returns: List of Reply objects.
        """
        path_query = "api/v1/replies"
        method = "GET"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        result = []
        for datum in response.data["replies"]:
            reply = Reply(**datum)
            result.append(reply)

        return result

    def download_reply(self, reply: Reply, original_path: str | None = None) -> tuple[str, str]:
        """
        Returns a tuple of etag (format is algorithm:checksum) and file path for
        a given Reply object. This method requires a directory path
        at which to save the reply file.

        :param reply: Reply object
        :param original_path: Local directory path to save the reply

        :returns: Tuple of etag and path of the saved Reply.
        """
        path_query = f"api/v1/sources/{reply.source_uuid}/replies/{reply.uuid}/download"

        method = "GET"

        if original_path:
            path = Path(original_path)
        else:
            path = Path("~/Downloads").expanduser()

        if not os.path.isdir(path):
            raise BaseError(f"Specified path isn't a directory: {path}")

        response = self._send_json_request(
            method,
            path_query,
            stream=True,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )

        if isinstance(response, JSONResponse):
            if response.status == 404:
                raise WrongUUIDError(f"Missing reply {reply.uuid}")
            else:
                raise BaseError(f"Unknown error, status code: {response.status}")

        filepath = path / reply.filename
        # reply.filename should have already been validated, but let's
        # double check before we write anything
        utils.check_path_traversal(filepath)
        filepath.write_bytes(response.contents)

        return response.sha256sum.strip('"'), str(filepath)

    def delete_reply(self, reply: Reply) -> bool:
        """
        Deletes a given Reply object from the server.

        :param reply: The Reply object we want to delete in the server.
        :returns: True if successful, raises Error otherwise.
        """
        # Not using direct URL because this helps to use the same method
        # from local reply (not fetched from server) objects.
        path_query = f"api/v1/sources/{reply.source_uuid}/replies/{reply.uuid}"

        method = "DELETE"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        if response.status == 404:
            raise WrongUUIDError(f"Missing reply {reply.uuid}")

        if response.data.get("message") == "Reply deleted":
            return True
        # We should never reach here
        return False

    def logout(self) -> bool:
        """
        Logs the current user out.
        """
        path_query = "api/v1/logout"
        method = "POST"

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        return response.data.get("message") == "Your token has been revoked."

    def seen(self, files: list[str], messages: list[str], replies: list[str]) -> str:
        """
        Mark supplied files, messages, and replies as seen by the current user. The current user
        will be retrieved from the auth header on the server.

        :param conversation_items: The items to mark as seen by the current user.
        :param files: list of file uuids to mark as seen
        :param messages: list of message uuids to mark as seen
        :param replies: list of reply uuids to mark as seen
        :returns: Raise exception if 404, else the direct response from the server
        """
        method = "POST"
        path_query = "api/v1/seen"
        body = json.dumps({"files": files, "messages": messages, "replies": replies})

        response = self._send_json_request(
            method,
            path_query,
            headers=self.build_headers(),
            body=body,
            timeout=self.default_request_timeout,
        )
        assert isinstance(response, JSONResponse)

        data_str = json.dumps(response.data)

        if response.status == 404:
            raise WrongUUIDError(f"{data_str}")

        # FIXME: why are we returning a string with a JSON-encoded blob???
        return data_str
