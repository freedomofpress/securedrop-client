import os


def pytest_unconfigure(config):
    if os.path.exists("login.txt"):
        os.unlink("login.txt")

    if os.path.exists("logout.txt"):
        os.unlink("logout.txt")
    if os.path.exists("testtoken.json"):
        os.unlink("testtoken.json")
    if os.path.exists("testtoken_http.json"):
        os.unlink("testtoken_http.json")
