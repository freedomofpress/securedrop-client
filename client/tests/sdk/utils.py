import json
import os
from collections import OrderedDict
from typing import Dict, Optional, Union
from unittest.mock import patch

import vcr
from vcr.request import Request

from securedrop_client.sdk import API, JSONResponse, StreamedResponse

VCR = vcr.VCR(cassette_library_dir="tests/sdk/data/")


class Cassette(vcr.cassette.Cassette):
    """Subclass `Cassette` to be able to handle two or more identical requests
    with different responses at different positions in the cassette.  Thanks to
    @vickyliin for suggesting this workaround for kevin1024/vcrpy#753."""

    def append_and_play(self, request, response) -> None:
        prev_len_data = len(self.data)
        super().append(request, response)
        is_appended = len(self.data) == prev_len_data + 1
        if is_appended:
            self.play_counts[prev_len_data] += 1

    def _load(self) -> None:
        super()._load()
        self.append = self.append_and_play
        self._load = None


class VCRAPI(API):
    """Subclass `API` so that `_send_json_request()` is instrumented to record
    and replay VCR.py cassettes.
    """

    def _send_json_request(
        self,
        method: str,
        path_query: str,
        stream: bool = False,
        body: Optional[str] = None,
        headers: Optional[Dict[str, str]] = None,
        timeout: Optional[int] = None,
    ) -> Union[StreamedResponse, JSONResponse]:
        """If the cassette contains a VCR.py `Request` object corresponding to
        this request, play back the response.  If it's an exception, raise it to
        be handled by the caller.

        Otherwise, make the request normally and record the response.  If it's
        an exception, record it anyway, then raise it to be handled by the
        caller.
        """

        request = Request(method, path_query, body, headers)

        # Playback mode:
        try:
            response = self._cassette.play_response(request)
            if isinstance(response, Exception):
                raise response

            return response

        # Request not in cassette; recording mode:
        except vcr.errors.UnhandledHTTPRequestError:
            try:
                response = super()._send_json_request(
                    method, path_query, stream, body, headers, timeout
                )
                self._cassette.append(request, response)
                return response

            except Exception as exc:
                self._cassette.append(request, exc)
                raise

    @staticmethod
    def use_cassette(func):
        """The decorated function `func` will be run with its corresponding
        cassette patched into place.
        """

        def wrapper(self, *args, **kwargs):
            # We have to specify an explicit path for each cassette because
            # we're not using vcr.use_cassette() directly as a decorator.
            context = VCR.use_cassette(f"{func.__name__}.yml")

            # Override `Cassette` to use our subclass before we enter the
            # context manager.
            context.cls = Cassette
            with context as cassette:
                with patch.object(VCRAPI, "_cassette", cassette, create=True):
                    return func(self, *args, **kwargs)

        return wrapper
