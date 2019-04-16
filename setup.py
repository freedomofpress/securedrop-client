import pkgutil
import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

version = pkgutil.get_data("securedrop_proxy", "VERSION").decode("utf-8")

setuptools.setup(
    name="securedrop-proxy",
    version=version,
    author="Freedom of the Press Foundation",
    author_email="securedrop@freedom.press",
    description="SecureDrop Qubes proxy service",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license="GPLv3+",
    install_requires=["requests", "furl", "pyyaml", "werkzeug"],
    python_requires=">=3.5",
    url="https://github.com/freedomofpress/securedrop-proxy",
    packages=setuptools.find_packages(exclude=["docs", "tests"]),
    classifiers=(
        "Development Status :: 3 - Alpha",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Intended Audience :: Developers",
        "Operating System :: OS Independent",
    ),
    entry_points={"console_scripts": ["sd-proxy = securedrop_proxy.entrypoint:start"]},
)
