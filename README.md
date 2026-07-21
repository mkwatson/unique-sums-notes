Notes on B. Bedert, "On unique sums in Abelian groups", Combinatorica 44 (2024) 269-298.

**[note.pdf](note.pdf)** (source: `note.tex`) is the write-up: two remarks on the paper, and
some further observations.

`SubsetSums.lean` is a machine-checked proof of the proposition in section 2, all but its
final, elementary Vandermonde step. The file ends with `#print axioms`, so building re-checks
it:

    lake exe cache get
    lake build

The build output should include

    'BedertLab.card_subsetSums_le' depends on axioms: [propext, Classical.choice, Quot.sound]

`verify.py` re-runs the arithmetic and the small computations (about 20 seconds, stdlib only):

    python3 verify.py

Mark Watson
