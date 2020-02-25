#!/bin/bash

# A script to run each functional test module (randomly ordered) in their own
# pytest process. Why? Because not all random combinations of these tests
# result in a passing suite (instead you get a core dump).

TESTFILES=$(find tests/functional/test_*.py -print | sort -R)
for f in $TESTFILES
do
    TEST_CMD=(python -m pytest -v --random-order-bucket global "$f")
    echo "${TEST_CMD[@]}"
    if command -v xvfb-run > /dev/null; then
        xvfb-run -a "${TEST_CMD[@]}"
    else
        "${TEST_CMD[@]}"
    fi
    if test $? -ne 0
    then
        exit 1
    fi
done
