from pprint import pprint
import os
import json
from subprocess import PIPE, Popen

from .sdlocalobjects import *

from typing import Optional, Dict, List, Tuple


def json_query(data):
    """
    Takes a json based query and passes to the network proxy.
    Returns the JSON output from the proxy.
    """
    proxyvmname = "proxy-debian"
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

    def authenticate(self, totp = "") -> bool:
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