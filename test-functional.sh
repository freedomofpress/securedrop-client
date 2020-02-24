# A script to run each functional test module (randomly ordered) in their own
# pytest process. Why? Because not all random combinations of these tests
# result in a passing suite (instead you get a core dump).

ls tests/functional/test_*.py |sort -R |tail -$N |while read file; do
    TEST_CMD="python -m pytest -v --random-order-bucket=global $file" ; \
    echo $TEST_CMD
    if command -v xvfb-run > /dev/null; then \
        xvfb-run -a $TEST_CMD ; else \
        $TEST_CMD ; fi
    if test $? -ne 0
    then
        exit 1
    fi
done
