#!/bin/sh
# Build GMP + MPFR + FLINT into a user-local prefix (no admin needed),
# for compiling powser_arnoldi on machines where you can't install packages.
#
#   PREFIX=$HOME/.local/powser sh build_deps.sh     (default shown)
#   then:  make server                              (static-links against PREFIX)
#
# Takes ~10-30 minutes depending on the machine.  Needs: gcc/cc, make,
# and curl or wget with network access.
#
# Before running this, check whether FLINT >= 3.0 is already available:
#   ls /usr/include/flint/acb_dft.h  ||  module avail 2>&1 | grep -i flint

set -e

PREFIX=${PREFIX:-$HOME/.local/powser}
JOBS=${JOBS:-4}

GMP_V=6.3.0
MPFR_V=4.2.1
FLINT_V=3.1.2

mkdir -p "$PREFIX/src"
cd "$PREFIX/src"

fetch() {
    f=$(basename "$1")
    # download to a temp name and move into place only on success, so an
    # interrupted transfer never leaves a partial file that a rerun would
    # mistake for a complete download (set -e + existence check)
    if [ ! -f "$f" ]; then
        if command -v curl >/dev/null 2>&1; then
            curl -L --fail --retry 8 --retry-delay 5 -C - -o "$f.part" "$1"
        else
            wget -c -O "$f.part" "$1"
        fi
        mv "$f.part" "$f"
    fi
}

fetch "https://gmplib.org/download/gmp/gmp-$GMP_V.tar.xz"
fetch "https://www.mpfr.org/mpfr-$MPFR_V/mpfr-$MPFR_V.tar.xz"
fetch "https://github.com/flintlib/flint/releases/download/v$FLINT_V/flint-$FLINT_V.tar.gz"

echo "=== building GMP $GMP_V ==="
rm -rf "gmp-$GMP_V"
tar xf "gmp-$GMP_V.tar.xz"
cd "gmp-$GMP_V"
./configure --prefix="$PREFIX" --enable-static --disable-shared >/dev/null
make -j"$JOBS" >/dev/null
make install >/dev/null
cd ..

echo "=== building MPFR $MPFR_V ==="
rm -rf "mpfr-$MPFR_V"
tar xf "mpfr-$MPFR_V.tar.xz"
cd "mpfr-$MPFR_V"
./configure --prefix="$PREFIX" --with-gmp="$PREFIX" --enable-static --disable-shared >/dev/null
make -j"$JOBS" >/dev/null
make install >/dev/null
cd ..

echo "=== building FLINT $FLINT_V ==="
rm -rf "flint-$FLINT_V"
tar xf "flint-$FLINT_V.tar.gz"
cd "flint-$FLINT_V"
./configure --prefix="$PREFIX" --with-gmp="$PREFIX" --with-mpfr="$PREFIX" \
    --enable-static --disable-shared >/dev/null
make -j"$JOBS" >/dev/null
make install >/dev/null
cd ..

echo "=== done: libraries in $PREFIX ==="
echo "now run:  make server    (or: make server PREFIX=$PREFIX)"
