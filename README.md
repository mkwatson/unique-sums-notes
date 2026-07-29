# Notes on unique sums

These are five short remarks on B. Bedert, “On unique sums in Abelian groups,”
Combinatorica 44 (2024), 269--298. The note records a 2-torsion scope issue in
one proof step, two observations confirmed by the author, an empty-set
convention, and exact values of \(m(p)\) through \(p=59\) with their
verification tiers.

To check the Lean proofs and the pure-Python computations:

```text
lake exe cache get
lake build
python3 verify.py
```

The Lean build prints the axiom sets for the principal results. They should be
exactly `[propext, Classical.choice, Quot.sound]`.

Changelog: v1, 2026-07-21; v2, 2026-07-29.

I made substantial use of AI tools. Mathematical claims were checked against
the cited sources, and the formal statements are checked by Lean.

Mark Watson
