# Belyi

Just download, and run magma in this directory attaching the spec: 
```
AttachSpec("Code/spec");
```

The following gives a basic test:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
// SetVerbose("Shimura", true);   (uncomment for verbose output)
X, phi := BelyiMap(sigma);
```

If you also have PARI/GP installed, there are significant performance improvements available (using `polredabs`). 
