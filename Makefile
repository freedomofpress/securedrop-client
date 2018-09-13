XARGS := xargs -0 $(shell test $$(uname) = Linux && echo -r)
GREP_T_FLAG := $(shell test $$(uname) = Linux && echo -T)
export PYFLAKES_BUILTINS=_

all:
	@echo "\nThere is no default Makefile target right now. Try:\n"
	@echo "make clean - reset the project and remove auto-generated assets."
	@echo "make test - run the unit test suite."
	@echo "make coverage - view a report on unit test coverage."
	@echo "make check  - run all checkers and tests."

clean:
	rm -rf build
	rm -rf dist
	rm -rf securedrop_client.egg-info
	rm -rf .coverage
	rm -rf .eggs
	rm -rf docs/_build
	rm -rf .pytest_cache
	rm -rf lib
	find . \( -name '*.py[co]' -o -name dropin.cache \) -delete
	find . \( -name '*.bak' -o -name dropin.cache \) -delete
	find . \( -name '*.tgz' -o -name dropin.cache \) -delete
	find . | grep -E "(__pycache__)" | xargs rm -rf

test: clean
	pytest

pyflakes:
	find . \( -name _build -o -name var -o -path ./docs -o -path \) -type d -prune -o -name '*.py' -print0 | $(XARGS) pyflakes

pycodestyle:
	find . \( -name _build -o -name var \) -type d -prune -o -name '*.py' -print0 | $(XARGS) -n 1 pycodestyle --repeat --exclude=build/*,docs/*,.vscode/* --ignore=E731,E402,W504

coverage: clean
	pytest --cov-config .coveragerc --cov-report term-missing --cov=securedrop_client tests/

check: clean pycodestyle pyflakes coverage
