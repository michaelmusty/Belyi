#!/bin/sh
# Test runner for the Belyi package.  Run from the repository root:
#   sh Tests/run_tests.sh
#   RUNSLOW=1 sh Tests/run_tests.sh
cd "$(dirname "$0")/.." || exit 1
FAILED=0

# ---- 1. C solver selftest -------------------------------------------------
BIN=${POWSER_ARNOLDI_BIN:-Cext/powser_arnoldi}
if [ ! -x "$BIN" ] && command -v make >/dev/null 2>&1; then
    (cd Cext && make powser_arnoldi >/dev/null 2>&1 || make mac >/dev/null 2>&1)
fi
# export an absolute path so the Magma tests (which read POWSER_ARNOLDI_BIN
# via GetEnv) actually use the binary we just built, instead of silently
# SKIPping when nothing named powser_arnoldi is on PATH
if [ -x "$BIN" ]; then
    POWSER_ARNOLDI_BIN="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
    export POWSER_ARNOLDI_BIN
fi
if [ -x "$BIN" ]; then
    if "$BIN" --selftest 2>&1 | grep -q "SELFTEST PASSED"; then
        echo "PASS: C solver selftest"
    else
        echo "FAIL: C solver selftest"
        FAILED=1
    fi
else
    echo "SKIP: C solver selftest (no binary; build Cext/powser_arnoldi)"
fi

# ---- 2. Magma tests -------------------------------------------------------
if ! command -v magma >/dev/null 2>&1; then
    echo "SKIP: Magma tests (magma not in PATH)"
    exit $FAILED
fi

run_magma_test() {
    f=$1
    # stdin from /dev/null: if a test errors into an interactive or debugger
    # prompt instead of quitting, it terminates on EOF rather than hanging
    # the runner with its output swallowed by the capture
    out=$(magma -b "$f" 2>&1 </dev/null)
    if echo "$out" | grep -q "ALL TESTS PASSED"; then
        echo "PASS: $f"
    elif echo "$out" | grep -q "^SKIP"; then
        echo "$out" | grep "^SKIP" | head -1
    else
        echo "FAIL: $f"
        echo "$out" | tail -25
        FAILED=1
    fi
}

run_magma_test Tests/test_basic_belyi.m
run_magma_test Tests/test_carnoldi_belyi.m
run_magma_test Tests/test_genusone_extra_zero.m
if [ -n "$RUNSLOW" ]; then
    run_magma_test Tests/test_powser_consistency.m
else
    echo "SKIP: Tests/test_powser_consistency.m (slow; set RUNSLOW=1)"
fi

exit $FAILED
