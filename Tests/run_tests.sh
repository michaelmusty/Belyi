#!/bin/sh
# Test runner for the Belyi package.  Run from the repository root:
#   sh Tests/run_tests.sh
#   RUNSLOW=1 sh Tests/run_tests.sh
cd "$(dirname "$0")/.." || exit 1
FAILED=0
now() { date +%s; }
SUITE_T0=$(now)

# ---- 1. C solver selftests ------------------------------------------------
BIN=${POWSER_ARNOLDI_BIN:-Cext/powser_arnoldi}
MBIN=${MAKEK_RELFINDER_BIN:-Cext/makek_relfinder}
# always invoke make (not only when a binary is missing): make no-ops when
# the binaries are up to date, and a stale binary from an older checkout
# silently reintroduces already-fixed bugs (observed: a pre-p-notation
# binary truncating all solver output to 30 digits).  Explicitly set
# POWSER_ARNOLDI_BIN / MAKEK_RELFINDER_BIN are respected and never rebuilt.
if { [ -z "${POWSER_ARNOLDI_BIN:-}" ] || [ -z "${MAKEK_RELFINDER_BIN:-}" ]; } \
   && command -v make >/dev/null 2>&1; then
    (cd Cext && { make >/dev/null 2>&1 || make mac >/dev/null 2>&1; })
fi
# export absolute paths so the Magma tests (which read these variables via
# GetEnv) actually use the binaries we just built, instead of silently
# SKIPping when nothing is on PATH
if [ -x "$BIN" ]; then
    POWSER_ARNOLDI_BIN="$(cd "$(dirname "$BIN")" && pwd)/$(basename "$BIN")"
    export POWSER_ARNOLDI_BIN
fi
if [ -x "$MBIN" ]; then
    MAKEK_RELFINDER_BIN="$(cd "$(dirname "$MBIN")" && pwd)/$(basename "$MBIN")"
    export MAKEK_RELFINDER_BIN
fi

selftest() {
    name=$1
    bin=$2
    if [ -x "$bin" ]; then
        t0=$(now)
        if "$bin" --selftest 2>&1 | grep -q "SELFTEST PASSED"; then
            echo "PASS: $name selftest ($(( $(now) - t0 )) s)"
        else
            echo "FAIL: $name selftest ($(( $(now) - t0 )) s)"
            FAILED=1
        fi
    else
        echo "SKIP: $name selftest (no binary; build Cext/$name)"
    fi
}
selftest powser_arnoldi "$BIN"
selftest makek_relfinder "$MBIN"

# ---- 2. Magma tests -------------------------------------------------------
if ! command -v magma >/dev/null 2>&1; then
    echo "SKIP: Magma tests (magma not in PATH)"
    exit $FAILED
fi

# run_magma_test <file> [legacy]
# "legacy" runs with MAKEK_RELFINDER_BIN emptied, exercising the pure-Magma
# recognition path even when the batched FLINT binary is available
run_magma_test() {
    f=$1
    mode=${2:-}
    tag=""
    # stdin from /dev/null: if a test errors into an interactive or debugger
    # prompt instead of quitting, it terminates on EOF rather than hanging
    # the runner with its output swallowed by the capture
    t0=$(now)
    if [ "$mode" = "legacy" ]; then
        tag=" (legacy MakeK)"
        out=$(env MAKEK_RELFINDER_BIN= magma -b "$f" 2>&1 </dev/null)
    else
        out=$(magma -b "$f" 2>&1 </dev/null)
    fi
    dt=$(( $(now) - t0 ))
    if echo "$out" | grep -q "ALL TESTS PASSED"; then
        echo "PASS: $f$tag ($dt s)"
    elif echo "$out" | grep -q "^SKIP"; then
        echo "$out" | grep "^SKIP" | head -1
    else
        echo "FAIL: $f$tag ($dt s)"
        echo "$out" | tail -25
        FAILED=1
    fi
}

run_magma_test Tests/test_basic_belyi.m
# with the binary exported above, the run above exercises the batched FLINT
# recognition; rerun through the legacy pure-Magma MakeK so BOTH paths stay
# covered (skipped when no binary: then the run above already was legacy)
if [ -n "${MAKEK_RELFINDER_BIN:-}" ]; then
    run_magma_test Tests/test_basic_belyi.m legacy
fi
run_magma_test Tests/test_carnoldi_belyi.m
run_magma_test Tests/test_genusone_extra_zero.m
run_magma_test Tests/test_genusone_aj.m
if [ -n "${MAKEK_RELFINDER_BIN:-}" ] && [ -x "$MAKEK_RELFINDER_BIN" ]; then
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

echo "total: $(( $(now) - SUITE_T0 )) s"
exit $FAILED
