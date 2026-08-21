# CENSSCHEMA: executable finite-Abelian census contract

Status: local handoff artifact under the outbound hold. This document specifies
an **ordered-representation** census. It uses the row layout of
`deliverable/mg-census-through-52.json`, but that older artifact's top-level
`convention` is not imported.

## 1. Problem, exactly

For a finite Abelian group `G` and a subset `A` of `G`, define

\[
R_A(s)=\#\{(a,b)\in A\times A:a+b=s\}.
\]

The pairs are ordered, diagonals are included, and all arithmetic is exact. A
nonempty set `A` is USF for this schema exactly when

\[
R_A(s)\notin\{1,2\}\quad\hbox{for every }s\in G.
\]

Equivalently, each count is zero or at least three. The often-used gloss “no
element has exactly one representation” is false for this predicate. In
`Z/11Z`, `A = {0,1,2,4,7}` has ordered count vector
`[3,2,3,3,3,2,2,2,3,2,0]`: it has no count-one fibre but is rejected because
several fibres have count two.

Define `m(G)` to be the minimum cardinality of a **nonempty** USF subset of
`G`. Write `null` if no such subset exists. Empty sets are never candidates.

## 2. Groups and canonical order

Every group is given in invariant-factor form

`G = C_n1 x ... x C_nr`, where `2 <= n1`, `ni | n(i+1)`.

The JSON field `moduli` is `[n1,...,nr]`, `order` is their product, and `group`
is exactly `C<n1>x...xC<nr>`. Enumerate orders increasingly, beginning at 2.
At a fixed order enumerate every Abelian isomorphism class once, sorted by
`(number_of_factors, moduli_lexicographically)`. This is the order produced by
`invariant_factor_groups` in `validator.py`.

Elements are integers `0 <= x < |G|`. Coordinates are row-major mixed radix:

`encode(c1,...,cr) = (((c1*n2 + c2)*n3 + c3)...)*nr + cr`.

Thus the last coordinate varies fastest. `decode` is repeated division from
the last modulus. Addition is coordinatewise modulo `moduli`, followed by
`encode`. Implementations must check both `decode(encode(c)) = c` and
`encode(decode(x)) = x` over every coordinate/element used.

## 3. Input

An engine receives one JSON object:

```json
{
  "schema": 1,
  "convention": "ordered pairs; R_A(s) is never 1 or 2",
  "min_order": 2,
  "max_order": 53,
  "groups": [[2], [3], [4], [2, 2]],
  "pruning": "none"
}
```

`groups` is optional. If absent, generate every canonical invariant-factor
group in the inclusive order interval. If present, it must equal a subsequence
of that canonical enumeration. `pruning` is either `"none"` or
`"retained-discard-records"`; any other value is rejected.

## 4. Output and merge contract

The top-level object follows schema 1 of the retained census:

```json
{
  "schema": 1,
  "convention": "ordered pairs; R_A(s) is never 1 or 2",
  "complete": true,
  "group_count": 1,
  "max_order_requested": 3,
  "results": [ROW],
  "stress_group_count": 0,
  "stress_results": []
}
```

Rows retain the existing keys `group`, `moduli`, `order`, `m`, `witness`,
`lower_bound`, `lower`, optional `upper`, and `tier`. Results are sorted by the
canonical group order. A solved row has integer `m`, a distinct in-range
integer witness of length `m`, and an identical witness in a SAT `upper`
record. `lower_bound` is `m-1`, and `lower` is an UNSAT record for the formula
“there exists a nonempty ordered-USF set of cardinality at most
`lower_bound`.” If `m` is `null`, `witness` and `upper` are absent/null and the
UNSAT bound must be `order`, proving nonexistence.

Every lower record supplies a certificate family:

```json
{
  "status": "UNSAT",
  "bound": 6,
  "formula": "cert/C11/at-most-6.cnf",
  "formula_sha256": "<64 lowercase hex>",
  "certificates": [
    {"path": "cert/C11/at-most-6.drat", "sha256": "<64 lowercase hex>",
     "checker": "drat-trim", "checker_result": "s VERIFIED"}
  ],
  "proof_verified": true,
  "witness": null
}
```

For merge compatibility the aliases `cnf`, `cnf_sha256`, `proof`, and
`proof_sha256` may also be present as in the existing artifact, but the
external package must include `formula`, `formula_sha256`, and nonempty
`certificates`. One at-most-`m-1` UNSAT certificate is mathematically enough
for all smaller cardinalities by monotonicity; “certificate family” means the
formula plus every proof/checker object needed to replay that lower-bound
claim. Paths are relative to the returned package root and hashes are SHA-256
of stored bytes.

The `upper` record has status `SAT`, the same witness as the row, and a
`model_membership` Boolean array of length `order` in element-index order.
This portable projection of the native model makes both directions testable:
the true positions must decode to `witness`, and encoding `witness` must recover
the identical Boolean array. The record may also carry the producing formula
and hashes. `tier` must describe only the evidence
actually returned; the expected retained tier for replayed witnesses and
checker-verified lower certificates is `EXACT COMPUTATION`.

## 5. Mandatory controls

Before admitting a row:

1. Directly recount its witness with ordered pairs and reject any fibre of
   size 1 or 2.
2. Decode `upper.model_membership` into a witness, recount it, then
   re-encode that witness and require exactly the same membership assignment.
3. For a claimed SAT formula, require its native model-to-membership adapter to
   produce `model_membership`, then require formula-to-model decoding to produce the
   stored witness. For a stored witness, fix the membership variables to that
   witness and require the formula to remain SAT. These are the two directions
   of the model check; witness recounting alone does not test the encoder.
4. Replay every lower certificate with the named checker, verify stored-byte
   hashes, and require the checker’s success token.
5. Run the false-gloss negative fixture. `run_controls.py` must report one
   attempted bad row and one fired rejection.

## 6. Pruning caveat

A certificate proves UNSAT only for the post-pruning formula that was emitted.
An unsound discarded symmetry/orbit/group can remove real witnesses and hence
inflate the reported `m(G)`. Prefer no pruning. If pruning is essential, retain
one machine-checkable record per discard: pre-pruning object, canonical image,
transform/inverse transform, and a check that the predicate and cardinality
are preserved. The certificate family and these discard records travel
together; a proof without them does not certify the unpruned problem.

## 7. Current continuation frontier

No continuation-frontier write-up existed at packaging time, so there is no
further result to cross-reference. The retained certified census is
contiguous through order 52. Its first unincluded group is `C53`: the known
exact-enumeration lower run has no retained DRAT certificate meeting the
census standard. The retained DCYC record therefore labels the frontier
`BLOCKED`, not timed out. This is the historical certificate frontier of the
existing unordered artifact; it is not evidence that the ordered schema has
been executed through 52.

## 8. Still undefined

The external engine and its native model/proof format are unknown. Therefore
the exact membership-variable map, SAT model syntax, checker executable and
version, certificate compression, resource limits, interruption protocol,
and per-discard record schema remain to be filled by the engine operator.
The schema also does not prescribe a symmetry-breaking method, a proof format
other than requiring a named independently replayable checker, or a policy
for merging conflicting rows. Those choices must be frozen before a run.

PHASE 1 DONE: ordered predicate, trap, group enumeration, element encoding,
`m(G)`, and row contract frozen.

PHASE 2 DONE: merge-compatible input/output contract and certificate-family
requirements frozen.

PHASE 3 DONE: bidirectional controls, pruning caveat, certified frontier, and
undefined engine interfaces recorded.
