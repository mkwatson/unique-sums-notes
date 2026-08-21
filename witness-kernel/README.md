# Witness and encoding kernel

This source-only Lean package contains the reference encoder specification, checks the six
published prime-cyclic witnesses and two retained local witnesses, and records the verified
parts of the production-encoding chain. Dependencies are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`; no `.lake` directory, dependency clone, or build
artifact belongs in the repository.

From this directory, fetch the pinned dependencies and run a single-module check:

```text
lake update
lake build BedertLab.EncodeSpec
lake env lean BedertLab/WitnessKernel.lean
lake env lean BedertLab/SequentialCounterProof.lean
```

The listed witness propositions, the universal at-most counter theorem
`SequentialCounterProof.atMostCorrect`, and the valid-domain exact counter theorem
`SequentialCounterProof.exactCorrect_of_le` are **KERNEL-CERTIFIED**. Every staged module
prints its axiom dependencies; the permitted set is exactly
`[propext, Classical.choice, Quot.sound]`, and individual declarations may use a subset.

The parser, scanner, clause-family, and embedded-byte modules preserve intermediate results
and named trust boundaries. They do not prove that the complete 5,652-byte production stream
parses to all 482 intended clauses, do not construct a complete `ProductionFamilies117`
instance, and do not close the full bytes-to-reference-specification theorem. The witness
results establish unique-sum-freeness only; they do not establish minimality, exhaustive lower
bounds, or equality for any value of $m(p)$.

## Independent kernel re-check (lean4checker)

Lean's own elaborator accepting a proof is one trust tier; an independently implemented
kernel-replay checker accepting the same compiled proof term is a stronger one, since it
does not share the elaborator's own code path. This package's 13 staged modules
(`ByteBridge`, `ByteBridgeAux`, `ChainClose`, `ClauseCorrespondence`, `EncodeSpec`,
`FamilyCertificate`, `FamilyCertificateTwo`, `ParsePath`, `ProjectionTheorem`,
`ScannerState`, `SequentialCounter`, `SequentialCounterProof`, `WitnessKernel`) were
diffed byte-for-byte against their source counterparts and confirmed identical, then
`lean4checker` (built at the matching `leanprover/lean4:v4.27.0` toolchain pinned by this
directory's own `lean-toolchain`) replayed the kernel judgment directly against the
already-built `.olean` files for these 13 modules, read-only, with no rebuild.

- **Positive control**: all 13 modules PASS (`lean4checker` exit 0 on each).
- **Negative control**: a doctored module asserting `False` from a mistyped term is
  correctly rejected (exit 1, `(kernel) declaration type mismatch`), confirming the
  checker is discriminating rather than fail-open.
- **Scope**: this re-check certifies that the kernel accepts the exact compiled proof
  terms already present in these 13 modules' `.olean` files. It does not rebuild the
  modules from the `.lean` source staged in this repository (byte-identity with the
  source that produced those `.olean` files is established separately, by the source
  diff above, not by the checker); it does not extend to any module outside this list;
  and it is a second run of the *same* toolchain's kernel, not a second, independently
  implemented proof system (that gold-standard tier is not claimed here).
