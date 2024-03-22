import json
import os
from collections import OrderedDict
from unittest.mock import MagicMock, patch

from securedrop_client.sdk import json_query

# We are making calls to securedrop.Proxy qrexec service
# in the QubesOS to get the data from the server. This is difficult to test
# unless we have an easy way to store/cache each function call and returned
# result. In this file we have a new decorator called `qrexec_datasaver`.
# This decorator checks for each json_query call and related arguments sent
# to the function, and then stores the result in a json file if required.
# From the next time, for the same signature, it will serve the result from the
# stored cache and will enable us to write unittests which can run without a
# real server.
# The result files will be stored in data/function_name.json files.

RES = {}
CALLNUMBER = 0


real_json_query = json_query


# This function obtains a JSON query result from the cache object (RES), or
# otherwise  performs a real query.
def mocked_json_query(*args, **kwargs):
    global CALLNUMBER
    CALLNUMBER += 1
    arguments = tuple(args)
    # Now remove the one time code
    # As it will be a different value every time.
    python_args = json.loads(args[1])

    try:
        value_str = python_args["body"]
        value = json.loads(value_str)
        del value["one_time_code"]
        python_args["body"] = json.dumps(value, sort_keys=True)
    except Exception:
        pass  # Means no body in the call

    # Now remove the authorization token from the key
    # Because in differnet runs, the token would be different
    # that is why we have to remove that.
    try:
        value = python_args["headers"]
        del value["Authorization"]
        python_args["headers"] = json.dumps(value, sort_keys=True)
    except Exception:
        pass  # Means no Authorization token in the call

    # Make sure the body is also sorted
    # This will work incase one_time_code is still missing
    # and there is a body in the call.
    try:
        value_str = python_args["body"]
        value = json.loads(value_str)
        dkeys = list(value.keys())
        dkeys.sort()
        print("\nDKEYS: ", dkeys)
        print("\n")
        od = OrderedDict()
        for k in dkeys:
            od[k] = value[k]
        python_args["body"] = json.dumps(od)
    except Exception:
        pass

    newargs = json.dumps(python_args, sort_keys=True)
    arguments = (newargs,)

    key = arguments[0] + "+" + str(CALLNUMBER)
    print(f"\nKEY:   {key}")
    answer = RES.get(key)
    if not answer:
        # Means it is not in cache.
        # So, execute the real function and store in cache
        answer = real_json_query(*args)
        RES[key] = answer
    return answer


def qrexec_datasaver(func):
    "This is the decorator to save qrexec call data"

    def wrapper(self, *args, **kwargs):
        global CALLNUMBER
        global RES
        # This is the filename to store the results
        filename = os.path.join("tests/sdk/data", func.__name__ + ".json")

        if os.path.exists(filename):
            with open(filename) as fobj:
                RES = json.load(fobj)
        mock = MagicMock()
        mock.side_effect = mocked_json_query
        with patch("securedrop_client.sdk.json_query", mock):
            result = func(self, *args, **kwargs)

        if not os.path.exists(filename):
            with open(filename, "w") as fobj:
                json.dump(RES, fobj)
        CALLNUMBER = 0
        return result

    return wrapper
