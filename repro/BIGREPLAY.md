# One-log theorem: 19-module closure replay

The one-log theorem's extracted, unconditional form (`sqrt_improvement_from_isUSF_internal`,
`RectificationInternal.lean`, a 19-module closure through `ObjectLayer/O7Headline.lean` and
`EncodeSpec.lean`) was written on a 16 GiB host and exceeds that host's memory. This page records
a fresh, independent replay of the same closure on a documented larger host, so a reader does not
have to trust the original elaboration alone.

## Host

```text
region: us-east-1
instance type: r8g.2xlarge, 8 vCPU, 64 GiB RAM, Graviton4
root volume: 60 GiB encrypted gp3, DeleteOnTermination=true
```

## Command sequence

From the project root (`lean/bedert-lab` in the full repository):

```bash
lake exe cache get
lake build +BedertLab.ObjectLayer.O7Headline +BedertLab.EncodeSpec

lake env lean -o .lake/build/lib/lean/BedertLab/RectificationInternal.olean \
  BedertLab/RectificationInternal.lean

lake env lean BedertLab/WitnessKernel.lean
```

The first command scopes the build to the target's own closure plus `WitnessKernel`'s one extra
dependency, `EncodeSpec`, while leaving `RectificationInternal.olean` and `WitnessKernel.olean`
themselves unbuilt. The second command is the guarded target elaboration itself. The third is a
positive control: an independent module in the same project, elaborated fresh against the closure
just built.

## Measured result

- Scoped build: 70 seconds, 7,903 jobs, exit 0.
- Target elaboration: 14 seconds, exit 0, measured peak resident set size about 7.3 GiB (well
  inside the 64 GiB host).
- All three required declarations -- `exists_source_fibre_selector_of_o7_cap_internal`,
  `sharpened_one_step_from_isUSF_internal`, `sqrt_improvement_from_isUSF_internal` -- print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `WitnessKernel` positive control: 26 seconds, exit 0, measured peak about 3.3 GiB.
- Negative control: a copy-only mutation of the frozen source (`129024 <= C` changed to
  `129025 <= C`) is correctly rejected by Lean with a genuine application type-mismatch
  diagnostic, not silently accepted.

This is the first complete replay of this module since the note was written. It does not change
the theorem's stated tier: the statement and its axioms are unchanged, and this page reports a
measurement, not a new proof.
