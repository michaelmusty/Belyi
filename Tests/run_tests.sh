#!/bin/sh
# Test runner for the Belyi package.  Run from the repository root:
#   sh Tests/run_tests.sh
#   RUNSLOW=1 sh Tests/run_tests.sh
cd "$(dirname "$0")/.." || exit 1
FAILED=0

# ---- 1. C solver selftests ------------------------------------------------
build_cext() {
    if command -v make >/dev/null 2>&1; then
        (cd Cext && make all >/dev/null 2>&1) || (cd Cext && make mac >/dev/null 2>&1) || true
    fi
}

BIN=${POWSER_ARNOLDI_BIN:-Cext/powser_arnoldi}
RELFINDER=${MAKEK_RELFINDER_BIN:-Cext/makek_relfinder}
if [ ! -x "$BIN" ] || [ ! -x "$RELFINDER" ]; then
    build_cext
fi
# export absolute paths so Magma tests (which read via GetEnv) actually use
# the binaries we just built, instead of silently falling back to legacy
if [ -x "$BIN" ]; then
    POWSER_ARNOLDI_BIN="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
    export POWSER_ARNOLDI_BIN
fi
if [ -x "$RELFINDER" ]; then
    MAKEK_RELFINDER_BIN="$(cd "$(dirname "$RELFINDER")" && pwd)/$(basename "$RELFINDER")"
    export MAKEK_RELFINDER_BIN
fi

if [ -x "${POWSER_ARNOLDI_BIN:-$BIN}" ]; then
    if "$POWSER_ARNOLDI_BIN" --selftest 2>&1 | grep -q "SELFTEST PASSED"; then
        echo "PASS: C powser_arnoldi selftest"
    else
        echo "FAIL: C powser_arnoldi selftest"
        FAILED=1
    fi
else
    echo "SKIP: C powser_arnoldi selftest (no binary; build Cext/powser_arnoldi)"
fi

if [ -x "${MAKEK_RELFINDER_BIN:-$RELFINDER}" ]; then
    if "$MAKEK_RELFINDER_BIN" --selftest 2>&1 | grep -q "SELFTEST PASSED"; then
        echo "PASS: C makek_relfinder selftest"
    else
        echo "FAIL: C makek_relfinder selftest"
        FAILED=1
    fi
else
    echo "SKIP: C makek_relfinder selftest (no binary; build Cext/makek_relfinder)"
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
if [ -n "$MAKEK_RELFINDER_BIN" ] && [ -x "$MAKEK_RELFINDER_BIN" ]; then
    run_magma_test Tests/test_makek_relfinder.m
    run_magma_test Tests/test_certified_belyi.m
else
    echo "SKIP: Tests/test_makek_relfinder.m (no MAKEK_RELFINDER_BIN)"
    echo "SKIP: Tests/test_certified_belyi.m (no MAKEK_RELFINDER_BIN)"
fi
if [ -n "$RUNSLOW" ]; then
    run_magma_test Tests/test_powser_consistency.m
else
    echo "SKIP: Tests/test_powser_consistency.m (slow; set RUNSLOW=1)"
fi

exit $FAILED
