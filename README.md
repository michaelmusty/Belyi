# Belyi

After cloning, include dependencies:
```
git submodule init
git submodule update --recursive --remote
```
This allows significant performance improvements using Pari/GP (using `polredabs`); the code will still run if you do not have Pari/GP installed.

After that, run magma in this directory attaching the spec: 
```
AttachSpec("Code/spec");
```

The following gives a basic test:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
// SetVerbose("Shimura", true);   (uncomment for verbose output)
X, phi := BelyiMap(sigma);
```

## Fast C solver for the power series basis

The dominant cost of `BelyiMap` is computing the numerical power series
basis (`PowerSeriesBasis`, Hejhal's method).  `Cext/` contains an external
C solver that performs this stage 10-20x faster by exploiting the structure
of the linear algebra (the circle points are exactly `rho` times the Q-th
roots of unity, so half the matrix-vector product is an FFT; the other half
is threaded polynomial evaluation) and by running multithreaded, which
Magma cannot.  The output is validated: the solver certifies each computed
basis vector by its residual, and the test suite checks that both pipelines
produce identical exact Belyi maps.

### Building

Requires [FLINT](https://flintlib.org) >= 3.0 (with MPFR and GMP).

Linux (with `libflint-dev` installed):
```
cd Cext && make
```

macOS (with `brew install flint mpfr gmp`):
```
cd Cext && make mac
```

On a server without admin rights, build the dependencies into your home
directory first (10-30 minutes, no root needed):
```
cd Cext && sh build_deps.sh && make server
```

Then check the build:
```
./powser_arnoldi --selftest    # should end with SELFTEST PASSED
```

### Using it from Magma

Export two environment variables in the shell that launches Magma (the
solver is invoked via `System`, which inherits the environment):
```
export POWSER_ARNOLDI_BIN=/path/to/Belyi/Cext/powser_arnoldi
export POWSER_ARNOLDI_THREADS=8      # threads for the solver; 8-16 is a
                                     # good choice, more rarely helps
```

Then pass `PowserAl := "CArnoldi"` to `BelyiMap`:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
X, phi := BelyiMap(sigma : PowserAl := "CArnoldi");
```
or call the basis computation directly with `Al := "CArnoldi"`:
```
Sk := PowerSeriesBasis(Gamma, k : dim := 2, Al := "CArnoldi");
```

The classical pure-Magma path remains the default (`PowserAl := "Arnoldi"`)
and is unchanged.  Timing reference: the degree-7 example of
Klug-Musty-Schiavone-Voight (Example 5.15, precision 100) runs end-to-end
in ~23 s with the C solver versus ~170 s without, on a 16-core machine.

Implementation notes, the input/output file formats, and numerical details
are documented in `Cext/README.md`.

## Tests

```
sh Tests/run_tests.sh              # quick tests
RUNSLOW=1 sh Tests/run_tests.sh    # includes the slow consistency test
```
See `Tests/README.md` for details.

