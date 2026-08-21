# Statement audit

This table is the audit surface a skeptical reader actually needs: for each
theorem cited in `note.tex` or checked by `witness-kernel/` or
`encoding-general/`, the exact formal
statement (file and line), what the cited check covers, what it does not
cover, and where the hereditary definitions used by that statement live. A
kernel checkmark certifies that a formal statement follows from the declared
definitions and axioms; it does not by itself certify that the formal
statement means what the surrounding English claims. Reading the statement
and its hereditary definitions, not the proof body, is the fast way to check
that correspondence yourself. `README.md`'s "Verification tiers" section
defines the tier vocabulary (kernel-certified, DRAT-certified, exact by
exhaustion, tested) used throughout.

## Part I: theorems cited in `note.tex`

| Claim (as stated in `note.tex`) | Formal statement | What the check covers | What it does not cover | Hereditary definitions |
|---|---|---|---|---|
| Sharp cyclic even-order boundary: for $m\geq0$, $\mathbb{Z}/(2m)\mathbb{Z}$ has a no-unique-sum set with an ordered representation count of 2 iff $m\geq6$ | `cyclicEven_orderedDivergence_iff`, `CycEven.lean:510` | Both directions of the iff, for every $m$, plus the exhaustive cases $2m<12$ | Nothing beyond the stated boundary; it does not address odd-order groups or unique-sum-freeness generally | `HasUniqueSum`, `IsUSF`, `orderedRepresentationCount`, `CycEven.lean:17-42` |
| Redundant factor in Proposition 1: $\lvert\Sigma(Z)\rvert\leq\binom{n+d}{d}$, dropping the first factor of Bedert's $\binom nd\binom{n+d}{d}$ | `card_subsetSums_le_card_dissocFamily`, `card_dissocFamily_le_sum_choose`, `SubsetSums.lean:101,112` | The first two inequalities in the displayed chain | The final step (the Vandermonde-style bound $\sum_{j\leq d}\binom nj\leq\binom{n+d}{d}$) is checked only by `verify.py`, not by Lean | `IsDissoc`, `dissocFamily`, `dissocDim`, `SubsetSums.lean:19-44` |
| Minima three and four: for every finite Abelian group $G$, $m(G)=3\iff3\mid\lvert G\rvert$, and $4\mid\lvert G\rvert\wedge3\nmid\lvert G\rvert\Rightarrow m(G)=4$ | `normalized_three_USF_has_three_torsion_unordered` (`Dcyc.lean:196`); `minUSFSize_C4_unordered`, `minUSFSize_C2xC2_unordered` (`Dcyc.lean:122,131`); `C12_refutes_unconditional_four_branch` (`Dcyc.lean:150`) | The three-set algebraic core, both order-four group cases ($C_4$ and $C_2\times C_2$), and the $C_{12}$ counterexample that rules out an unguarded general four-branch | The general-$G$ statement itself is elementary prose (see `note.tex`'s proof), assembled from these certified pieces by hand, not by one Lean theorem that quantifies over all finite Abelian groups | `IsUSF`, `HasMinUSFSize`, `Dcyc.lean:19-33` |
| Census-52: all 88 groups of order $\leq52$ plus 26 stress groups through order 221 match the min-over-prime-divisors formula | No Lean theorem; each of the 114 lower bounds has a retained DRAT unsatisfiability certificate, replayed by an independent checker | 114 exact groups, each individually DRAT-certified; hashes, paths, and outcomes recorded in `mg-census-through-52.json` (SHA-256 quoted in `note.tex`). The 36 further certified groups of the 2026-08-21 extension run are recorded separately in `mg-census-extension-2026-08-21.json`; they are additional data points for the same formula, not part of the note's Census-52 claim, and they do not extend the contiguous range | Not a theorem for all finite Abelian groups; the DRAT proofs themselves are not distributed, only their hashes; the encoding/checker trust surfaces are the ones named in Part II below, not re-derived per group | N/A (data manifest, not a Lean statement) |
| Double-cyclic conjecture evidence: every minimum set in $C_2\times C_p$ lies in one parity fibre, checked for $p\in\{3,\ldots,29\}$; the $C_2\times C_{11}$ projection counterexample | `C2xC3_bounded_USF_localizes_unordered` (`Dcyc.lean:273`, the $p=3$ instance); the counterexample construction `A2x11`, `B11` (`Dcyc.lean:66-105`) | The Lean theorem covers the $p=3$ instance and the stated counterexample exactly; the extension through $p=29$ is DRAT search evidence outside Lean, not re-proved for each prime in this module | Does not prove the conjecture; the empty-overlap reduction that would close it is stated as proved prose in `note.tex`, not as a single Lean theorem here | `IsUSF`, `PairClosed`, `MeetsBothParityFibers`, `Dcyc.lean:19,230,268` |
| One-log improvement: $K(A)>\sqrt{M/404}$ under the stated hypotheses | Conditional: `sqrt_improvement_from_isUSF_proposed`, `BedertLab/ObjectLayer/O7Headline.lean:29`. Extracted (no `hBLR` binder): `sqrt_improvement_from_isUSF_internal`, `BedertLab/RectificationInternal.lean:453` | The conditional statement is freshly kernel-checkable on request. The extracted statement's 19-module import closure was kernel-certified at its original elaboration; both print exactly `[propext, Classical.choice, Quot.sound]` (full closure record in `README.md`) | The conditional form assumes the Lev rectification interface `hBLR`, which is not established anywhere in this development; the extracted form removes that binder but is not freshly re-verifiable on a 16 GiB host and is included for inspection, not fresh replay | `K(A)` and the ambient hypotheses are defined across the `ObjectLayer` chain; the closure list is in `README.md`'s tier note for this theorem |

Claims stated in `note.tex` without a Lean formalization are tiered accordingly in the note itself and are not restated here as if Lean-backed: the Łuczak and Schoen transfer (published theorem plus elementary transfer), the Cao and Yuan comparison (source-grounded adjudication of an unrefereed preprint), the Palomar entry (kernel-replayed on this hardware, not a re-derivation), and the simultaneous-selector threshold (exhaustive computation at 29 primes plus a hand proof, explicitly not kernel-certified).

## Part II: the SAT-encoding verification chain (`witness-kernel/BedertLab/`)

These modules back the encoding-verification claims described in `README.md`'s Layout table, not any claim in `note.tex` itself. The chain identifies where the encoder-to-DIMACS trust boundary currently sits; it does not close it.

| Claim | Formal statement | What the check covers | What it does not cover | Hereditary definitions |
|---|---|---|---|---|
| A machine-checked encoder specification | `satisfies_encode_iff`, `exists_model_iff_exists_target`, `EncodeSpec.lean:116,140` | Correctness of the exponential reference encoder against the ordered-representation definition | Does not address the production (Sinz sequential-counter) encoder actually used by the search, which is a separate, differently structured encoding | `HasUniqueSum`, `IsUSF`, `Target`, `EncodeSpec.lean:20-71` |
| A kernel-certified correctness theorem for the sequential-counter cardinality encoding the search actually uses | `atMostCorrect`, `SequentialCounterProof.lean:252`; `exactCorrect_of_le`, `SequentialCounterProof.lean:351` | At-most correctness holds universally; exact correctness is proved for $k\leq n$, which covers the production instance $(n,k)=(11,7)$ | Does not itself connect the counter encoding to the parsed DIMACS byte stream; that link is `ClauseCorrespondence.lean`, below | `AtMostSat`, `AtMostCorrect`, `ExactSat`, `ExactCorrect`, `SequentialCounter.lean:39,69,92,98` |
| Kernel-checked proofs that all six published witnesses are unique-sum-free | `published53_isUSF` .. `published73_isUSF`, `WitnessKernel.lean:61-66` | Unique-sum-freeness of the six published witness sets ($p=53,59,61,67,71,73$) by `decide` | No minimality or lower-bound claim; establishes the witnesses are valid, not that they are smallest | `IsUSF`, `WitnessKernel.lean:19`, proved definitionally equal to the reference spec by `isUSF_iff_encodeSpec`, `WitnessKernel.lean:28` |
| Pair-variable projection theorem underlying the pruning-certificate replayer | `productionPair_projectsTo`, `ProjectionTheorem.lean:205` | The production-size ($n=11$) instance of the general pair-projection theorem (`pair_projectsTo`, line 137) | Certifies the pair-variable projection only; does not certify the external search engine that generates the pruning certificates replayed in `pruning-handshake/` | `ProjectsTo` (`ProjectionTheorem.lean:35`); `ProductionPairVariable`, `productionPairLeft`, `productionPairRight` (`ProjectionTheorem.lean:192-200`) |
| The 165-clause pair block of the production CNF | `satisfies_pairClauses_iff`, `pairClauses_card`, `FamilyCertificate.lean:118,136` | Exact clause count (165) and a semantic-equivalence theorem for this clause family | Certifies this one clause family only, not the encoding's other clause families or their union | `PairSat117`, `ClauseSatisfied`, `FamilyCertificate.lean:93,112` |
| The Sinz counter and USF-diagonal clause families | `positiveSinz_card`, `negativeSinz_card`, `usfClauses_card`, `FamilyCertificateTwo.lean:80,83,108` | Exact clause counts for each family (157, 94, 66 respectively) | Constructs these families but does not prove their semantic equivalence to the counter/diagonal specifications, and there is deliberately no theorem for the full union's cardinality | `sinzClauses`, `usfClauses`, `FamilyCertificateTwo.lean:75,100` |
| The byte-to-specification bridge is the trust boundary that remains open | Target obligation `Production117BytesToSpec` (`ByteBridgeAux.lean:145`, a definition, not a theorem); conditional theorem `production117_composes` (`ByteBridgeAux.lean:156`); conditional theorem `production117BytesToSpec_of_parse_and_families` (`ClauseCorrespondence.lean:123`) | Identifies the exact trust boundary and proves it conditionally on successful parsing plus a complete `ProductionFamilies117` certificate | Does not close the obligation: nothing in this development constructs a `ProductionFamilies117` instance for the actual production bytes, so the unconditional bytes-to-spec theorem remains unproved | `RawDIMACS` (`ByteBridge.lean:75`), `ProjectsToReference` (`ByteBridgeAux.lean:103`) |
| The production instance's literal byte stream | `production117String`, `production117Bytes`, `ChainClose.lean:19,40` | Confirms the exact production byte sequence is embedded and available to the chain above | No parse theorem: embedding the bytes is not the same as proving they parse to the intended clause set | N/A (data definitions) |
| Bounded prefix parsing | `production117_prefix5_body_parses`, `ParsePath.lean:26` | The first 5 clauses of the production byte stream parse as intended | Bounded to a 5-clause prefix; does not extend to the full 482-clause production stream | `production117Prefix5`, `ParsePath.lean:23` |
| Generic resumable-parser theory | `tokenize_eq_finish_scan`, `parseBodyChars_eq_stepped`, `ScannerState.lean:57,169` | Generic theorems that a resumable (chunked) scan agrees with a one-shot scan, for arbitrary input | Generic parser theory only; supplies no concrete-byte certificate for the production stream itself | `State` (`ScannerState.lean:21-24`), `ClauseState` (`ScannerState.lean:108-111`) |
| Deliberately broken encoder variants are all caught | Executable `run_mutation_suite` (`encoding-tests/mutation_harness.py`); formal reference `satisfies_encode_iff` (`EncodeSpec.lean:116`) | **Tested, not proved:** all fixed mutations are detected within the recorded finite range ($p\leq13$); see `encoding-tests/README.md` for the exact count and the traced survivors | Finite differential testing, not a Lean proof; does not extend to primes outside the tested range | N/A (test harness, not a formal statement) |
| Parser/printer self-consistency on the DIMACS text this encoder emits | Executable `roundtrip_control.py` (`encoding-tests/roundtrip_control.py`) | **Tested, not proved:** parse-then-print-then-reparse agreement on a spread of `(p, k)` pairs, plus a deliberate-corruption negative control that is correctly refused | Does not test the Lean-side scanner/parser in `ScannerState.lean`; a separate, Python-only parser/printer pair, exercised only at the tested `(p, k)` values | N/A (test harness, not a formal statement) |

## Part III: the parse-level byte-tamper theorem (cloud-checked, not yet staged in this repository)

This theorem is checked in the author's private development lab and on a
documented cloud host, not in this repository's `witness-kernel/` package: it
bears on the same encoder-to-DIMACS trust boundary Part II audits, but its
source has not yet been independently replayed on this note's author's own
local machine and is not shipped alongside the 13 modules listed there.
`README.md`'s "Verification tiers" section defines its tier,
kernel-checked-on-cloud, distinct from kernel-certified for exactly that
reason.

| Claim | Formal statement | What the check covers | What it does not cover | Hereditary definitions |
|---|---|---|---|---|
| A single flipped literal in the production DIMACS bytes is caught by parsing, not silently accepted | `tampered_production117_parse_fails`, `ChainCloseTamper.lean:23` (private lab; imports the frozen target `ChainTamperStage.lean`) | For one specific one-byte tamper (byte 0 of `chunk00`, the first of the production stream's nineteen scan chunks), the tampered scan is proved to diverge from the untampered target. Checked kernel-checked-on-cloud: exit 0, 32 seconds, peak resident set size about 8.0 GiB, exactly the permitted axiom set `[propext, Classical.choice, Quot.sound]`; a fresh `WitnessKernel` build on the same host printed no axiom outside that set across every checked declaration | Tests only this one tamper position; does not generalize to a tamper at an arbitrary byte or to multi-byte tampers, and is not a general parser-soundness theorem. Not independently replayed on this note's own local machine, so not described as kernel-certified. Does not by itself close the byte-to-specification bridge in Part II, which remains open | `tamperedState01`&ndash;`tamperedState19` (the nineteen-state scan) and the eighteen-step transition/survival chain, `ChainTamperStage.lean`; built on the generic resumable-parser theory in `ScannerState.lean`, audited in Part II above |

## Part IV: the general finite-group encoding layer (`encoding-general/BedertLab/`)

Part II's chain is stated for the carrier $\mathbb{Z}/n\mathbb{Z}$ and for the fixed
cyclic unique-sum-free target. The five theorems below are the same reference-encoder
statements with both of those fixed choices removed: the carrier is any type with
`AddCommGroup`, `Fintype` and `DecidableEq`, and the target is any
`predicate : Finset G → Prop` with `DecidablePred predicate`. Like Part II, they back
`README.md`'s Layout table rather than any claim in `note.tex`.

Three limits apply to every row and are not repeated in each one. The encoder is the
exponential reference encoder only, with one blocking clause per falsifying subset and no
auxiliary variables; it is not the production encoder any search runs. The argument that
this predicate interface lines up with the ordered representation count used elsewhere in
this repository is single-arm prose with no Lean statement, so it is not kernel-certified.
And the production serialization bridge is untouched: the round-trip control uses the
generalized raw reference fixture serializer, not production bytes, so the
bytes-to-specification obligation in Part II is exactly as open as before.

| Claim | Formal statement | What the check covers | What it does not cover | Hereditary definitions |
|---|---|---|---|---|
| A full blocking clause is falsified by exactly one membership pattern, over any finite Abelian group | `eval_blockingClause_false_iff`, `encoding-general/BedertLab/EncodeGen.lean:57` | For every such group, every assignment and every subset: the clause has no satisfied literal exactly when the assignment decodes to that subset | Says nothing about any encoder built from these clauses; that is the next row | `Literal`, `Clause`, `evalLiteral`, `decode`, `blockingClause`, `EncodeGen.lean:17,23,27,41,46` |
| The generalized reference encoder is pointwise faithful to the caller's predicate | `satisfies_encode_iff`, `encoding-general/BedertLab/EncodeGen.lean:95` | For every finite Abelian group and every decidable subset predicate: an assignment satisfies the encoded CNF exactly when its decoded subset satisfies the predicate | Does not address any compact or production encoding, which is differently structured, and does not by itself give a satisfiability statement | `Satisfies`, `decode`, `encode`, `EncodeGen.lean:31,41,51` |
| The generalized reference encoding is equisatisfiable with the caller's predicate | `exists_model_iff_exists_predicate`, `encoding-general/BedertLab/EncodeGen.lean:120` | For every finite Abelian group and every decidable subset predicate: the CNF has a Boolean model exactly when some finite subset satisfies the predicate | Gives no bound on CNF size, which is exponential by construction, and supplies no solver-side or certificate-side guarantee | `Satisfies`, `encode`, `EncodeGen.lean:31,51` |
| The generalized witness checker accepts exactly the valid witnesses | `checkWitness_eq_true_iff`, `encoding-general/BedertLab/EncodeGenWitness.lean:19` | Acceptance is exact for every finite Abelian group, every decidable subset predicate and every candidate subset | Establishes that a supplied witness satisfies the predicate; no minimality, lower-bound or exhaustiveness claim follows | `checkWitness`, `EncodeGenWitness.lean:14` |
| Rejection by the generalized witness checker is exact | `checkWitness_eq_false_iff`, `encoding-general/BedertLab/EncodeGenWitness.lean:26` | Rejection is exact at the same generality, so a refused subset provably fails the predicate rather than merely failing to be recognized | Does not certify that the predicate a caller supplies is the property they meant; that correspondence is the reader's, as everywhere in this table | `checkWitness`, `EncodeGenWitness.lean:14` |

The controls in `encoding-general/BedertLab/EncodeGenControls.lean` are what makes the
five rows above evidence about the generalization rather than about the case it came
from: they run on the noncyclic group $\mathbb{Z}/2\mathbb{Z}\times\mathbb{Z}/2\mathbb{Z}$
(`KleinFour`, line 147) against the unrelated predicate `anchoredPair` (line 156), not on
a cyclic group and not on unique-sum-freeness. `witness_positive_control` (line 180) is
the positive control, `klein_dimacs_round_trip_control` (line 256) proves the exact
serialize-parse-to-CNF route returns the intended CNF, and five mutations are proved to
fire: `cardinality_mutation_fires` (186), `omitted_blocking_clause_mutation_fires` (193),
`polarity_mutation_fires` (203), `dimacs_literal_mutation_fires` (263) and
`dimacs_header_mutation_fires` (271). All are kernel-certified at the tier `README.md`
defines, with axiom prints within `[propext, Classical.choice, Quot.sound]`;
`encoding-general/README.md` lists the exact expected lines and the command that emits
them. Unlike the 13 modules of Part II, these have not been replayed by `lean4checker`.

## What each claim changes

The tables above say what a claim is and what its check covers. This list says
what each one changes for a reader, in one line and one of four categories:
*witness only* (a verified data point, no new general statement), *scope
repair* (an existing published statement gains or loses a hypothesis, or a
route is closed by a counterexample), *reusable mechanism* (a construction or
audit surface someone else can pick up), *theory change* (a general statement
that was not previously available).

| Claim | Category | What changes |
|---|---|---|
| Sharp cyclic even-order boundary | scope repair | The step "no unique sum implies balanced" needs an odd-order clause; the even-order boundary is now pinned exactly, so the published step can be restated with a hypothesis that is not merely sufficient |
| Redundant factor in Proposition 1 | scope repair | One of the two binomial factors in the published bound is unnecessary; the bound holds as stated but is not the sharpest the argument gives |
| Minima three and four for all finite Abelian groups | theory change | The question moves from $\mathbb{Z}/p\mathbb{Z}$ to every finite Abelian group with exact answers at the bottom of the scale, where before there were none |
| Census-52 and the 2026-08-21 extension | witness only | Verified data points consistent with the min-over-prime-divisors formula; no general statement follows, and the contiguous range is unchanged at order 52 |
| Double-cyclic localization evidence and the $C_2\times C_{11}$ counterexample | scope repair | The counterexample closes the full-double-lift route to the double-cyclic conjecture; the localization data is a witness only and proves nothing beyond the primes searched |
| One-log improvement | theory change, since superseded | It removed one logarithm from the published dissociation bound; its asymptotic role in bounding $m(p)$ is now superseded by Cao and Yuan and by the Palomar entry, while its own statement and tier stand |
| The SAT-encoding chain of Part II | reusable mechanism | It names, in machine-checkable form, exactly where the encoder-to-DIMACS trust boundary sits, so a reader auditing a solver-backed claim can start from the boundary rather than from the whole pipeline |
| The general finite-group encoding layer of Part IV | reusable mechanism | The reference-encoder correctness and witness-checking statements stop being about $\mathbb{Z}/p\mathbb{Z}$ and unique-sum-freeness, so someone encoding a different subset property over a different finite Abelian group can reuse the proofs instead of rewriting them; the trust boundary itself is unmoved |
| The parse-level byte-tamper theorem of Part III | reusable mechanism | It converts one instance of "the bytes were not silently corrupted" from an assumption into a checked statement, at one tamper position; the boundary itself stays open |

## What this table is not

This is a statement-and-scope audit, not a proof-body audit: it does not
substitute for reading the referenced files, and it does not certify that
these are the only trust boundaries in the packet. Toolchain pin, axiom
prints, and the independent kernel re-check for these 13 modules are in
`witness-kernel/README.md`. Part III's theorem is checked separately, at the
tier stated there, and is not part of that 13-module recheck. Part IV's
package pins the same toolchain and prints its own axiom lines, listed in
`encoding-general/README.md`, and is likewise outside the 13-module recheck.
