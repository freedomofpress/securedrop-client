import pkgutil

version = pkgutil.get_data("securedrop_proxy", "VERSION").decode("utf-8")
