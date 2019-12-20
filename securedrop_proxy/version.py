import pkgutil

version = None
version_content = pkgutil.get_data("securedrop_proxy", "VERSION")
if isinstance(version_content, bytes):
    version = version_content.decode("utf-8")
else:
    raise ValueError("Could not read VERSION file")
