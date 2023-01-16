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

