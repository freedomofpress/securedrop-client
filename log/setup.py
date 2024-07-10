import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="securedrop-log",
    version="0.0.0",
    author="Freedom of the Press Foundation",
    author_email="securedrop@freedom.press",
    description="SecureDrop Qubes logging scripts",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license="GPLv3+",
    install_requires=[],
    python_requires=">=3.5",
    packages=setuptools.find_packages(exclude=["docs", "tests"]),
    url="https://github.com/freedomofpress/securedrop-log",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Intended Audience :: Developers",
        "Operating System :: POSIX :: Linux",
    ],
    data_files=[("sbin", ["securedrop-log", "securedrop-log-saver", "securedrop-redis-log"])],
)
