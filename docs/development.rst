Development
============

This project uses `pipenv <https://docs.pipenv.org>`_ to manage all dependencies.
This is a Python 3 project. When using ``pipenv`` locally, ensure you used the ``--keep-outdated``
flag to prevent dependencies from being unnecessarily upgraded during normal development.

We cover all the API calls supported by the SecureDrop Journalist Interface API.

Git clone the project repo, and use the following command to create a new dev
environment. The second command is to enable the virtual environment.

.. code:: sh

    pipenv sync --dev
    pipenv shell


Testing
========

The tests are located in the ``tests`` directory. This project uses `vcrpy
<http://vcrpy.readthedocs.io/en/latest/>`_ to record and then reply the API calls so that
developers will have repeatable results so that they may work offline. ``vcrpy`` stores YAML
recordings of the API calls in the ``data`` directory. 

To run all the test cases, use the following command.

.. code:: sh

    make test

To run a single test, use this following command, replace the test case name at the end.

.. code:: sh

    make test TESTS=tests/test_api.py::TestAPI::test_error_unencrypted_reply


To test against a live development server, you will need to run the SecureDrop developent
container from the main SecureDrop repository on your host. This can be done via ``make -C securedrop dev``.

In this repo, comment out the ``@vcr`` decorator of the ``setUp`` method and which ever tests
you want to run. If you want to re-run all tests against the API, remove all the ``.yml`` files
in the ``data`` directory. 

Releasing
=========

To make a release, you should:

1. Update the version in ``setup.py``
2. Update the changelog
3. Commit the changes, and ``git tag``.
4. Create a PR, push the new tag, and get the PR reviewed and merged into ``master``.
5. Push the new release to the PSF's PyPI `following this documentation <https://packaging.python.org/tutorials/packaging-projects/#uploading-the-distribution-archives>`_.
