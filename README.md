# Notes on unique sums in Abelian groups

These are notes and verification artifacts on B. Bedert, "On unique sums in
Abelian groups," *Combinatorica* 44 (2024), 269--298
([doi:10.1007/s00493-023-00069-w](https://doi.org/10.1007/s00493-023-00069-w),
[arXiv:2303.15134](https://arxiv.org/abs/2303.15134)).

A set $A$ in an Abelian group is unique-sum-free when every element of $A+A$
has at least two genuinely different representations. The paper studies $m(p)$,
the smallest size of such a set in $\mathbb{Z}/p\mathbb{Z}$. Green lists the question as Problem
27 of his 100 open problems.

**The write-up is [note.pdf](note.pdf)** (source `note.tex`). Everything in it
was produced while checking the paper's argument line by line, and every claim
carries an exact verification tier. The repository holds the evidence for each
tier, including the parts that fall short of proof, so a skeptical reader can
see not only what was checked but what was not.

## What came of checking

Reading the printed proof produced two corrections. The step "no unique sum
implies balanced" needs an odd-order clause: there is an explicit 7-element
counterexample in $\mathbb{Z}/12\mathbb{Z}$, and the even-order boundary is sharp, with a
kernel-certified proof in `CycEven.lean`. And the $(\log p)^2$ order of the
paper's upper bound already follows from a 2008 theorem of Łuczak and Schoen
that the paper does not cite; the author has confirmed this observation. A
third observation removes a redundant binomial factor from Proposition 1.

Extending the question from $\mathbb{Z}/p\mathbb{Z}$ to general finite Abelian groups gave exact
answers at the bottom of the scale: $m(G) = 3$ if and only if 3 divides $|G|$,
and $m(G) = 4$ whenever 4 divides $|G|$ and 3 does not. The three-set case is a
three-line argument forcing $3x = 0$; the algebraic cores are kernel-certified
in `Dcyc.lean`.
A census of all 88 Abelian groups of order at most 52, plus 26 stress groups
through order 221, matches the natural minimum-over-prime-divisors formula,
with a retained DRAT proof for each of the 114 lower bounds.

On the asymptotic side the note proves a one-log sharpening of the paper's
dissociation bound. Within weeks, two stronger results appeared: a
preprint of Cao and Yuan (arXiv:2608.06728) and a
Lean-formalized theorem of Xinjie He registered on the Palomar registry,
which together move the lower bound to $c(\log p/\log\log p)^2$ and pin the
exponent of $\log p$. The note states both at full strength, records exactly
what supersedes what, and keeps the overtaken theorem at its unchanged tier.
The exact-value table $m(3) = 3$ through $m(59) = 15$ stands regardless; those
sixteen values also appear in Scheinerman's dissertation, and what this
repository adds is the retained evidence.

## Verification tiers

Every claim is labeled. The vocabulary, strongest first:

- **kernel-certified**: the exact statement is proved in Lean 4; zero sorries,
  no new axioms, and `#print axioms` shows at most
  `[propext, Classical.choice, Quot.sound]`.
- **DRAT-certified**: an exhaustive search whose unsatisfiability certificate
  is retained and replayed by an independent proof checker. The encoding,
  the checker, and the statement bridge remain trusted surfaces, and the
  `witness-kernel/` and `encoding-tests/` directories are the audit of
  exactly those surfaces.
- **exact by exhaustion**: a completed search whose code and outputs are
  retained but which produced no independent certificate. $m(53)$ and $m(59)$
  are at this tier and are never described as certified.
- **tested**: finite differential testing with negative controls. Test
  results are reported as found, including the four mutation-test survivors
  in `encoding-tests/`, each traced to a provably redundant clause.

Downgrades are recorded in place. One Lean module (the one-log theorem's
19-module closure) is included at the tier "recorded original elaboration"
because it exceeds the memory of the 16 GiB host it was written on; the
checking section of the note says exactly which command verifies which tier.

[`statement-audit.md`](statement-audit.md) gives the exact formal statement,
file, and line for every theorem cited above and in `note.tex`, alongside
what its check covers, what it does not, and where its hereditary
definitions live, so a claim can be audited without reading the proof body.

## Layout

| Directory | Contents | Check with |
|---|---|---|
| `note.pdf`, `note.tex` | The four-part write-up | read it |
| root Lean files | Kernel cores for the note (`Dcyc.lean`, `CycEven.lean`, `SubsetSums.lean`, `Headline.lean`) | `lake exe cache get && lake build` |
| `verify.py` | Pure-Python recomputation of every small case and table | `python3 verify.py` |
| `witness-kernel/` | Encoder specification and the certified parts of the encoding chain, with named trust boundaries | `lake update && lake build BedertLab.EncodeSpec` |
| `encoding-tests/` | The pinned production encoder, a differential oracle test at $p \le 13$, and a 34-mutant harness | `python3 mutation_harness.py` |
| `pruning-handshake/` | Replayable soundness evidence for symmetry pruning, with negative controls | `python3 pruning_handshake_replay.py HANDSHAKE-p11-k7-v2.jsonl` |
| `census-schema/` | Row format and validator for the finite-group census | `python3 run_controls.py` |
| `provenance/` | Retained outputs of the $m(53)$ and $m(59)$ exhaustive runs and witness rechecks | `provenance/README.md` |
| `repro/` | One deterministic command that reruns the computational claims, with a deliberately failing control that must fire | `./repro/run.sh` |
| `mg-census-through-52.json` | Census manifest: CNF and DRAT SHA-256 hashes for all 114 groups | hashes within |

The census DRAT proofs themselves are retained locally and are not
distributed; the manifest records their hashes. Python bytecode caches
(`__pycache__/`, `*.pyc`), produced by running the scripts above locally, are
excluded from the staged tree; none should appear in a push from this
repository.

## Method

I made substantial use of AI tools throughout, under a fixed discipline:
claims are stated with the strongest verification available and never above
it, machine-checkable claims are machine-checked, searches carry negative
controls that must fail, and corrections to the record are kept, not
overwritten. Mathematical claims were checked against the cited sources, and
the formal statements are checked by Lean.

Mark Watson
