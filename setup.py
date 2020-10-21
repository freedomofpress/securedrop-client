import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="securedrop-sdk",
    version="0.2.0",
    author="Freedom of the Press Foundation",
    author_email="securedrop@freedom.press",
    description="Python client API to access SecureDrop Journalist REST API",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license="GPLv3+",
    install_requires=["requests", "urllib3"],
    python_requires=">=3.5",
    url="https://github.com/freedomofpress/securedrop-sdk",
    packages=setuptools.find_packages(exclude=["docs", "tests"]),
    classifiers=(
        "Programming Language :: Python :: 3",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Intended Audience :: Developers",
        "Operating System :: OS Independent",
    ),
)
