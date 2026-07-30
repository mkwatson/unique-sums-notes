# Notes on unique sums

These are notes on B. Bedert, "On unique sums in Abelian groups,"
Combinatorica 44 (2024), 269--298
([doi:10.1007/s00493-023-00069-w](https://doi.org/10.1007/s00493-023-00069-w),
[arXiv:2303.15134](https://arxiv.org/abs/2303.15134)).

**The four-part write-up is [note.pdf](note.pdf)**, with source in `note.tex`.
Part I records corrections and scope; Part II gives results and evidence for
the general-group question the paper poses; Part III gives two prime-cyclic
sharpenings; Part IV is the current table of \(m(p)\). Every claim carries
its verification tier and scope.

To check the Lean proofs and pure-Python computations:

```text
lake exe cache get
lake build
python3 verify.py
```

`Headline.lean` imports a self-contained 19-module extraction of the
unconditional headline theorem. `Dcyc.lean` contains the finite-group kernel
cores. The principal axiom prints should be exactly
`[propext, Classical.choice, Quot.sound]`.

The Census-52 DRAT proofs are retained locally and are not distributed.
Their paths and SHA-256 hashes are recorded in
`mg-census-through-52.json`.

Changelog: v1, 2026-07-21; v2, 2026-07-29; staged v3, 2026-07-29.

I made substantial use of AI tools. Mathematical claims were checked against
the cited sources, and the formal statements are checked by Lean.

Mark Watson
