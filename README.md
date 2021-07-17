# Belyi

Just download, and run magma in this directory attaching the spec: 
```
AttachSpec("Code/spec");
```

The following gives a basic test:
```
sigma := [Sym(4) | (1,2,3,4), (1,3,4,2), (1,3,4)];
Gamma := TriangleSubgroup(sigma);
SetVerbose("Shimura", true);
X, phi := BelyiMap(Gamma);
```
