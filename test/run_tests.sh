#!/bin/bash
# ToyC compiler test runner
# Usage:
#   ./test/run_tests.sh          # compile + show assembly
#   ./test/run_tests.sh -gcc     # compile with gcc and run (needs gcc)
#   ./test/run_tests.sh -rars    # compile with toyc, parse with rars (needs rars1_6.jar)

set -e

TOYC="./toyc"
TESTDIR="test"
GCC_RESULTS=""
TOYC_RESULTS=""
PASS=0
FAIL=0

echo "=============================="
echo "  ToyC Compiler Test Runner"
echo "=============================="
echo ""

for tc in ${TESTDIR}/*.tc; do
    base=$(basename "$tc" .tc)
    echo -n "[$base] "

    if [ "$1" = "-gcc" ]; then
        # Compile with gcc and run
        gcc -x c -w "$tc" -o "/tmp/toyc_test_gcc" 2>/dev/null
        if [ $? -ne 0 ]; then
            echo "GCC COMPILE FAIL"
            FAIL=$((FAIL + 1))
            continue
        fi
        expected=$(/tmp/toyc_test_gcc 2>/dev/null; echo $?)
        echo "expected=$expected"
        PASS=$((PASS + 1))
    elif [ "$1" = "-rars" ]; then
        # Compile with toyc, then run with RARS
        if ! "$TOYC" < "$tc" > "/tmp/toyc_test.s" 2>/dev/null; then
            echo "TOYC COMPILE FAIL"
            FAIL=$((FAIL + 1))
            continue
        fi
        result=$(java -jar rars1_6.jar sm "/tmp/toyc_test.s" 2>/dev/null | tail -1)
        echo "result=$result"
        PASS=$((PASS + 1))
    else
        # Default: just compile with toyc, verify it succeeds
        if "$TOYC" < "$tc" > "/tmp/toyc_test_${base}.s" 2>/tmp/toyc_err; then
            lines=$(wc -l < "/tmp/toyc_test_${base}.s")
            echo "OK (${lines} lines)"
            PASS=$((PASS + 1))
        else
            err=$(cat /tmp/toyc_err)
            echo "FAIL: $err"
            FAIL=$((FAIL + 1))
        fi
    fi
done

echo ""
echo "=============================="
echo "  Results: $PASS passed, $FAIL failed"
echo "=============================="
