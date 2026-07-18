# External C solver for the Arnoldi stage of PowerSeriesBasis
# (used by Al := "CArnoldi" in Code/powser_iter_arfed.m)
#
# Linux:  make            (needs libflint-dev >= 3.0, libmpfr-dev, libgmp-dev)
# macOS:  make mac        (brew install flint mpfr gmp)
# Test:   make test

CC = gcc
CFLAGS = -O2 -pthread
LIBS = -lflint -lmpfr -lgmp -lm

powser_arnoldi: powser_arnoldi.c
	$(CC) $(CFLAGS) powser_arnoldi.c -o powser_arnoldi $(LIBS)

mac: powser_arnoldi.c
	clang -O2 -pthread powser_arnoldi.c -o powser_arnoldi \
	  -I$$(brew --prefix flint)/include -L$$(brew --prefix flint)/lib \
	  -I$$(brew --prefix mpfr)/include -L$$(brew --prefix mpfr)/lib \
	  -I$$(brew --prefix gmp)/include  -L$$(brew --prefix gmp)/lib \
	  $(LIBS)

bench: powser_bench.c
	$(CC) $(CFLAGS) powser_bench.c -o powser_bench $(LIBS)

test: powser_arnoldi
	./powser_arnoldi --selftest

clean:
	rm -f powser_arnoldi powser_bench

.PHONY: mac test clean
