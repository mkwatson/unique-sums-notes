# Changes from v1 to staged v2

- Replaced the broad “Further observations” section with three signal-first
  items: the 2-torsion proof-scope issue, the empty-set convention, and the
  updated \(m(p)\) table.
- Dropped all four v1 proof-mechanics subsections: shift-set growth, branch
  increments, the \(\omega_1\) conversion discussion, and the limiting
  construction. They are outside the five-item boundary for this revision.
- Added the complete \(C_{12}\) representation table and stated explicitly
  that the example does not dispute the general lower-bound theorem itself.
- Added the sharp cyclic even-order boundary and its machine-checked proof.
- Tightened the Łuczak--Schoen and Proposition 1 sections to record the
  author's confirmations without quoting private correspondence.
- Added the empty-set issue in the balanced-set definition and proposition.
- Extended the exact-value table through \(p=59\). The table now separates
  certified values from exact-by-exhaustion values and avoids v1's flattened
  “certified optimal” description.
- Carried over `SubsetSums.lean`; added standalone `CycEven.lean` and the
  concrete `C12Witness.lean`.
- Extended `verify.py` with the full \(C_{12}\) table check and frontier
  witness checks while retaining every v1 check that remains relevant.
