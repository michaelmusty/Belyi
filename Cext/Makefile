# External C solvers:
#   powser_arnoldi  -- Arnoldi stage of PowerSeriesBasis
#                      (used by Al := "CArnoldi" in Code/powser_iter_arfed.m)
#   makek_relfinder -- batched certified recognition for the MakeK stage
#                      (used when MAKEK_RELFINDER_BIN is set; see Code/theta.m)
#
# Linux:  make            (needs libflint-dev >= 3.0, libmpfr-dev, libgmp-dev)
# macOS:  make mac        (brew install flint mpfr gmp)
# Test:   make test

CC = gcc
CFLAGS = -O2 -pthread
LIBS = -lflint -lmpfr -lgmp -lm

BREWFLAGS = -I$$(brew --prefix flint)/include -L$$(brew --prefix flint)/lib \
	  -I$$(brew --prefix mpfr)/include -L$$(brew --prefix mpfr)/lib \
	  -I$$(brew --prefix gmp)/include  -L$$(brew --prefix gmp)/lib

all: powser_arnoldi makek_relfinder

powser_arnoldi: powser_arnoldi.c
	$(CC) $(CFLAGS) powser_arnoldi.c -o powser_arnoldi $(LIBS)

makek_relfinder: makek_relfinder.c
	$(CC) $(CFLAGS) makek_relfinder.c -o makek_relfinder $(LIBS)

mac: powser_arnoldi.c makek_relfinder.c
	clang -O2 -pthread powser_arnoldi.c -o powser_arnoldi $(BREWFLAGS) $(LIBS)
	clang -O2 -pthread makek_relfinder.c -o makek_relfinder $(BREWFLAGS) $(LIBS)

# For servers without admin access: first run  sh build_deps.sh  to build
# GMP/MPFR/FLINT into PREFIX, then this target static-links against them
# (no LD_LIBRARY_PATH needed at runtime).
PREFIX ?= $(HOME)/.local/powser
STATICLIBS = -I$(PREFIX)/include \
	  $(PREFIX)/lib/libflint.a $(PREFIX)/lib/libmpfr.a $(PREFIX)/lib/libgmp.a -lm
server: powser_arnoldi.c makek_relfinder.c
	$(CC) $(CFLAGS) powser_arnoldi.c -o powser_arnoldi $(STATICLIBS)
	$(CC) $(CFLAGS) makek_relfinder.c -o makek_relfinder $(STATICLIBS)

bench: powser_bench.c
	$(CC) $(CFLAGS) powser_bench.c -o powser_bench $(LIBS)

test: powser_arnoldi makek_relfinder
	./powser_arnoldi --selftest
	./makek_relfinder --selftest

clean:
	rm -f powser_arnoldi powser_bench makek_relfinder

.PHONY: all mac test clean server
