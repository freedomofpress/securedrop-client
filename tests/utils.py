import os
import json
from pprint import pprint
from sdclientapi import json_query
from unittest.mock import MagicMock, patch

from typing import Optional, Dict, List, Tuple

# We are making calls to securedrop.Proxy qrexec service
# in the QubesOS to get the data from the server. This is difficult to test
# unless we have an easy way to store/cache each function call and returned
# result. In this file we have a new decorator called `dastollervey_datasaver`.
# This decorator checks for each json_query call and related arguments sent
# to the function, and then stores the result in a json file if required.
# From the next time, for the same signature, it will serve the result from the
# stored cache and will enable us to write unittests which can run without a
# real server.
# The result files will be stored in data/function_name.json files.

RES = {}
CALLNUMBER = 0


alternative = json_query


def internal_sideeffect(*args, **kwargs):
    global CALLNUMBER
    global RES
    CALLNUMBER += 1
    arguments = tuple(args)
    # Now remove the one time code
    # As it will be a different value every time.
    python_args = json.loads(args[0])

    try:
        value_str = python_args["body"]
        value = json.loads(value_str)
        del value["one_time_code"]
        python_args["body"] = json.dumps(value)
        newargs = json.dumps(python_args)
        arguments = (newargs,)
    except:
        pass  # Means no body in the call

    # Now remove the authorization token from the key
    # Because in differnet runs, the token would be different
    # that is why we have to remove that.
    try:
        value = python_args["headers"]
        del value["Authorization"]
        python_args["headers"] = json.dumps(value)
        newargs = json.dumps(python_args)
        arguments = (newargs,)
    except Exception as err:
        pass  # Means no Authorization token in the call

    key = str((arguments, CALLNUMBER))
    answer = RES.get(key, None)
    if not answer:
        # Means it is not in cache.
        # So, execute the real function and store in cache
        answer = alternative(*args)
        RES[key] = answer
    return answer


def dastollervey_datasaver(func):
    "This is the decorator to save qrexec call data"

    def wrapper(*args, **kwargs):
        global CALLNUMBER
        global RES
        # This is the filename to store the results
        filename = os.path.join("data", func.__name__ + ".json")

        if os.path.exists(filename):
            with open(filename) as fobj:
                RES = json.load(fobj)
        mock = MagicMock()
        mock.side_effect = internal_sideeffect
        with patch("sdclientapi.proxyapi.json_query", mock):
            result = func(*args, **kwargs)

        if not os.path.exists(filename):
            with open(filename, "w") as fobj:
                json.dump(RES, fobj)
        CALLNUMBER = 0
        return result

    return wrapper
