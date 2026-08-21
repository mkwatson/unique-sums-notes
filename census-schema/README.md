# Census schema

`SCHEMA.md` defines the ordered-count census row format. `validator.py` checks row shape,
group encoding, witness recounts, and the declared tier. Run `python3 run_controls.py` for
one accepted row and one deliberately rejected false-gloss row.

The validator is **TESTED, not PROVED**. It does not certify an external engine, its native
model, its certificates, or the production encoding consumed by a solver.
