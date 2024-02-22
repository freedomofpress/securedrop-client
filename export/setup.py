import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="securedrop-export",
    version="0.0.0",
    author="Freedom of the Press Foundation",
    author_email="securedrop@freedom.press",
    description="SecureDrop Qubes export scripts",
    long_description=long_description,
    long_description_content_type="text/markdown",
    license="GPLv3+",
    install_requires=[],
    python_requires=">=3.5",
    url="https://github.com/freedomofpress/securedrop-export",
    packages=setuptools.find_packages(exclude=["docs", "tests"]),
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Programming Language :: Python :: 3",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "License :: OSI Approved :: GNU General Public License v3 or later (GPLv3+)",
        "Intended Audience :: Developers",
        "Operating System :: OS Independent",
    ],
    entry_points={
        "console_scripts": ["send-to-usb = securedrop_export.main:entrypoint"]
    },
)
