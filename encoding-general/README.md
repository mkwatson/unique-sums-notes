# General finite-group encoding layer

This source-only Lean package generalizes the reference-encoder surface audited in
`witness-kernel/`. That package fixes the carrier to $\mathbb{Z}/n\mathbb{Z}$ and fixes
the encoded target to the cyclic unique-sum-free predicate. This one fixes neither. The
carrier is any type `G` carrying `AddCommGroup G`, `Fintype G` and `DecidableEq G`, and
the encoded target is any `predicate : Finset G → Prop` carrying
`DecidablePred predicate`. The encoder, its faithfulness theorem, its equisatisfiability
theorem and the witness checker are all stated at that generality, so a reader with a
different group and a different subset property can reuse them without editing a proof.

The same generalization applies to the differential testing in `encoding-tests/`: that
directory tests one pinned production encoder for one predicate at $p\le13$, while the
statements here quantify over the group and the predicate but describe the exponential
reference encoder only, not any production encoder.

Dependencies are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`,
which are byte-identical to `witness-kernel/`'s. No `.lake` directory, dependency clone,
or build artifact belongs in the repository.

## What is in the package

| Module | Contents |
|---|---|
| `BedertLab/EncodeGen.lean` | Generalized `Literal`, `Clause`, `CNF`, `Satisfies`, `decode`, `blockingClause`, `encode`, and the three correctness theorems |
| `BedertLab/EncodeGenWitness.lean` | The generalized witness checker `checkWitness` and its two exactness theorems |
| `BedertLab/EncodeGenControls.lean` | Klein-four controls: a positive witness control, a strict DIMACS round trip, and five firing mutations |
| `BedertLab/EncodeSpec.lean` | Vendored prerequisite, byte-identical to `witness-kernel/BedertLab/EncodeSpec.lean` |
| `BedertLab/ByteBridge.lean` | Vendored prerequisite, byte-identical to `witness-kernel/BedertLab/ByteBridge.lean`; supplies the frozen strict DIMACS tokenizer and raw parser the controls reuse |

The two vendored modules are copies, not forks. They are present because
`EncodeGenControls.lean` reuses the existing frozen byte front end rather than writing a
second tokenizer, and a reader should be able to build this directory on its own.

## The encoder and what is proved about it

`encode G predicate` emits one full blocking clause for every subset of `G` at which the
predicate is false. A full blocking clause names every element of the group, positively
when the element is outside the blocked subset and negatively when it is inside, so it is
falsified by exactly one membership pattern. The three theorems in `EncodeGen.lean` are:

- `eval_blockingClause_false_iff`: a blocking clause is unsatisfied under an assignment
  exactly when the assignment decodes to the subset that clause names;
- `satisfies_encode_iff`: an assignment satisfies the encoded CNF exactly when the subset
  it decodes to satisfies the caller's predicate;
- `exists_model_iff_exists_predicate`: the CNF has a Boolean model exactly when some
  finite subset of `G` satisfies the predicate.

`EncodeGenWitness.checkWitness` is the corresponding acceptance test on a supplied
subset. `checkWitness_eq_true_iff` and `checkWitness_eq_false_iff` prove that acceptance
and rejection are both exact, again for every finite abelian group and every decidable
subset predicate.

These seven statements are **kernel-certified** in the sense `README.md`'s
"Verification tiers" section defines: zero sorries, no new axioms, no `native_decide`,
and `#print axioms` within `[propext, Classical.choice, Quot.sound]`. They are checked by
the one Lean toolchain pinned in this directory's `lean-toolchain`, so the trust basis is
one implementation, not multi-verifier consensus.

## The noncyclic control

Every finite control in `EncodeGenControls.lean` runs on the Klein four group
`KleinFour := ZMod 2 × ZMod 2`, which is deliberately not cyclic, against the predicate
`anchoredPair A := A.card = 2 ∧ (0,0) ∈ A`, which is deliberately not unique-sum-freeness.
A layer that claimed generality but was exercised only on $\mathbb{Z}/n\mathbb{Z}$ and only
on the original target would be testing the special case it came from. Choosing a
noncyclic group and an unrelated predicate is what makes the controls evidence about the
generalization rather than about the instance.

The DIMACS control uses a proof-carrying duplicate-free enumeration of the whole group
(`kleinNumbering`, whose `nodup` and `complete` fields are discharged by `decide`), a
list-based raw DIMACS value, a decimal serializer, the frozen strict parser, and the
conversion into generalized literals. `klein_dimacs_round_trip_control` proves that the
route from raw clauses through a DIMACS character stream, a strict parse, generalized
literals and the generalized CNF returns the exact intended CNF.

Five mutations are proved to fire, and each is a theorem, not a test run:

| Theorem | What it breaks |
|---|---|
| `cardinality_mutation_fires` | An off-by-one predicate (`card = 1`) accepts a witness the intended predicate rejects |
| `omitted_blocking_clause_mutation_fires` | Deleting the empty-subset blocking clause creates a satisfying assignment that decodes to a bad subset |
| `polarity_mutation_fires` | Reversing every blocking-clause polarity accepts a bad subset whose complement satisfies the predicate |
| `dimacs_literal_mutation_fires` | Changing DIMACS literal `-2` to `-3` changes the parsed clause list |
| `dimacs_header_mutation_fires` | Changing the header `cnf` to `cxf` is refused rather than parsed |

`witness_positive_control` is the matching positive control: the checker accepts a valid
Klein-four witness.

## Verifying it

From this directory, fetch the pinned dependencies and run the single build command. The
build itself prints every axiom dependency, because the `#print axioms` commands are in
the modules.

```text
lake update
lake exe cache get
lake build BedertLab.EncodeGen BedertLab.EncodeGenWitness BedertLab.EncodeGenControls
```

The build reports `Build completed successfully (1102 jobs)` and no warnings. On the
author's machine, against already-fetched pinned dependencies, the third command took
6.3 seconds from a cleared build directory and 0.7 seconds on warm replay; the three
modules elaborate individually under `lake env lean` in 1.6, 1.3 and 3.0 seconds.

Among the axiom lines the build prints, these sixteen cover every public theorem the
package adds:

```text
'BedertLab.EncodeGen.eval_blockingClause_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGen.satisfies_encode_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGen.exists_model_iff_exists_predicate' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenWitness.checkWitness_eq_true_iff' depends on axioms: [propext, Quot.sound]
'BedertLab.EncodeGenWitness.checkWitness_eq_false_iff' depends on axioms: [propext, Quot.sound]
'BedertLab.EncodeGenControls.witness_positive_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenControls.cardinality_mutation_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenControls.omitted_blocking_clause_mutation_fires' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BedertLab.EncodeGenControls.polarity_mutation_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenControls.klein_dimacs_chars_to_raw_control' depends on axioms: [propext]
'BedertLab.EncodeGenControls.klein_dimacs_render_control' does not depend on any axioms
'BedertLab.EncodeGenControls.klein_raw_to_clause_lists_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BedertLab.EncodeGenControls.klein_dimacs_clause_round_trip_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BedertLab.EncodeGenControls.klein_dimacs_round_trip_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenControls.dimacs_literal_mutation_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
'BedertLab.EncodeGenControls.dimacs_header_mutation_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one is a subset of `[propext, Classical.choice, Quot.sound]`; individual
declarations use less. Lake prefixes each line with `info:` and a file position, and
wraps long lists across lines exactly as shown above. A source scan of the three added
modules finds zero `sorry`, zero `native_decide` and zero new `axiom` declarations.

## Using it for your own group and predicate

Import `BedertLab.EncodeGenWitness` and supply two things: an instance chain
`AddCommGroup G`, `Fintype G`, `DecidableEq G` for your carrier, and a predicate on
`Finset G` with a `DecidablePred` instance. Nothing else in the package is specialized to
the Klein four group; `EncodeGenControls.lean` is a worked example rather than a
dependency.

The block below is verbatim the contents of a file that elaborates in this package with
`lake env lean`, in 1.5 seconds measured. The `ZMod` import is needed because
`BedertLab.EncodeGenWitness` does not pull it in.

```lean
import Mathlib.Data.ZMod.Basic
import BedertLab.EncodeGenWitness

open BedertLab.EncodeGen BedertLab.EncodeGenWitness

abbrev G := ZMod 3 × ZMod 3

def myPredicate (A : Finset G) : Prop := A.card = 4 ∧ (0, 0) ∉ A

instance (A : Finset G) : Decidable (myPredicate A) := by
  unfold myPredicate; infer_instance

example : checkWitness G myPredicate {(1,0), (2,0), (0,1), (0,2)} = true := by decide

example (A : Finset G) :
    Satisfies (fun x => decide (x ∈ A)) (encode G myPredicate) ↔
      myPredicate (decode G (fun x => decide (x ∈ A))) :=
  satisfies_encode_iff G myPredicate _
```

Two practical notes. The encoder is exponential by construction, so `decide` on the full
CNF is only tractable for small groups; the controls here raise `maxRecDepth` to 100000
for a group of order four. And `Numbering G`, which the DIMACS layer takes, carries
proofs that the supplied variable order is duplicate-free and covers the whole group, so
a wrong or partial variable order is refused rather than silently accepted.

## Scope

Three limits travel with everything above, and none of them is closed by this package.

1. **Exponential reference encoder only.** `encode` emits one clause per falsifying
   subset and introduces no auxiliary variables. It is a semantic specification to test
   production encoders against, in the same role `witness-kernel/BedertLab/EncodeSpec.lean`
   plays for the cyclic case. It is not a compact encoding and is not the encoder any
   search in this repository runs.

2. **The ordered-count equivalence is proved in prose, not kernel-certified.** The
   argument that the generalized predicate interface lines up with the ordered
   representation count used elsewhere in the repository exists as a single-arm prose
   proof. It has no Lean statement here, so it sits below the kernel-certified tier and
   should be read as unformalized.

3. **The production serialization bridge remains open.** The serializer exercised by the
   round-trip control is the generalized raw reference fixture serializer and nothing
   more. It does not connect a compact production encoder, an auxiliary-variable layout,
   ordinary file input and output, or solver-consumed production bytes to the proved
   predicate semantics. The bytes-to-specification obligation that
   `witness-kernel/README.md` and `statement-audit.md` Part II identify as open is exactly
   as open after this package as before it. Nothing here should be read as narrowing it.
