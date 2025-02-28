
# HoTTLean 
## *Formalizing the Meta-Theory of HoTT in Lean4*

This repository formalizes in Lean4 the groupoid model of HoTT.
A web version of the mathematics, `lean4` documentation, and a dependency graph on the progress of formalization can be found
[here](https://sinhp.github.io/groupoid_model_in_lean4/).

This is intended to serve as the basis for a HoTT mode in Lean.

This repository relies on the [formalization of polynomial functors](https://github.com/sinhp/Poly/tree/master).

To get the most recent changes of the polynomial functors repository, run `lake update` first in the terminal inside the VSCode.
You should see a message like

```
info: Poly: updating repository '././.lake/packages/Poly' to revision '7297691124d30c971ff69d691e6cbd35e9a5bcac'
```

To get mathlib cached `.olean` files run

```
lake exe cache get
```


and to get the cached files and override your potentially corrupted `.olean` files run

```
lake exe cache get!
```
