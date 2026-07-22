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

`bedert-lab/` is a second, self-contained Lean project: the working development that the
remark in section 3 of the note mentions as not yet included. `BedertLab/Iteration.lean`
states the two-branch reading of Proposition 6 as one explicit hypothesis (`TwoBranchStep`,
the single statement to check against the paper) and derives the improved exponent from it,
kernel-checked end to end, together with the growth bound for arbitrary schedules
(`bookkeeping`) and the abstract iteration bound. Building it re-checks everything:

    cd bedert-lab
    lake exe cache get
    lake build

The build output should include

    'BedertLab.milestone3' depends on axioms: [propext, Classical.choice, Quot.sound]

Mark Watson
