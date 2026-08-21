#!/usr/bin/env python3
"""Round-trip (parse -> print -> reparse) control for the DIMACS encoding.

A proof-assistant or checker convention is not "well-behaved" by default: an
unverified parser/printer pair can silently disagree with itself, which is
exactly how a false statement can slip past a checker that trusts its own
serialization (Pollack-inconsistency). Nothing else in this repository checks
that property for the encoder used here. `witness-kernel/BedertLab/ScannerState.lean`
and `ByteBridgeAux.lean` prove the *parser* correct against a reference
scan and show that a tampered literal is detected; neither proves
parse(print(parse(x))) == parse(x) for the DIMACS text this encoder actually
emits, which is the standard round-trip property this script checks directly
against the pinned production encoder (`usf_encode_pinned.py`).

Positive control: for a spread of (p, k) pairs, encode to DIMACS text, parse
it, print the parsed structure back out, reparse, and require the two
parses to be identical.

Negative control: take one well-formed DIMACS text, corrupt its declared
header clause count without touching the body, and require the parser to
raise rather than silently accept the mismatch. A parser that "fixed" or
ignored the corruption would defeat the point of the positive control above.
"""
import sys

from usf_encode_pinned import encode


class DimacsError(ValueError):
    """Raised when input is not well-formed DIMACS CNF."""


def parse_dimacs(text):
    """Strict DIMACS CNF parser. Returns (nvars, declared_nclauses, clauses)."""
    header = None
    clauses = []
    current = []
    body_started = False
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("c"):
            if body_started:
                raise DimacsError("comment line after body started")
            continue
        if line.startswith("p"):
            if header is not None:
                raise DimacsError("duplicate header line")
            parts = line.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise DimacsError(f"malformed header: {line!r}")
            header = (int(parts[2]), int(parts[3]))
            continue
        if header is None:
            raise DimacsError("clause line before header")
        body_started = True
        for tok in line.split():
            v = int(tok)
            if v == 0:
                clauses.append(tuple(current))
                current = []
            else:
                if abs(v) > header[0]:
                    raise DimacsError(
                        f"literal {v} out of declared range 1..{header[0]}"
                    )
                current.append(v)
    if current:
        raise DimacsError("trailing clause missing terminating 0")
    if header is None:
        raise DimacsError("missing header line")
    nvars, declared_nclauses = header
    if len(clauses) != declared_nclauses:
        raise DimacsError(
            f"declared clause count {declared_nclauses} does not match "
            f"body clause count {len(clauses)}"
        )
    return nvars, declared_nclauses, tuple(clauses)


def print_dimacs(nvars, clauses):
    out = [f"p cnf {nvars} {len(clauses)}"]
    out += [" ".join(map(str, c)) + " 0" for c in clauses]
    return "\n".join(out) + "\n"


def round_trip_matches(text):
    nvars1, ncl1, clauses1 = parse_dimacs(text)
    reprinted = print_dimacs(nvars1, clauses1)
    nvars2, ncl2, clauses2 = parse_dimacs(reprinted)
    return nvars1 == nvars2 and ncl1 == ncl2 and clauses1 == clauses2


def run_positive_control():
    cases = [(p, k) for p in (3, 5, 7, 11, 13) for k in range(2, p)]
    for p, k in cases:
        text = encode(p, k).dimacs()
        if not round_trip_matches(text):
            raise SystemExit(f"POSITIVE control FAILED at p={p} k={k}")
    print(
        f"POSITIVE control: {len(cases)}/{len(cases)} (p, k) pairs "
        "round-trip exactly (parse == parse(print(parse(x))))"
    )


def run_negative_control():
    text = encode(11, 7).dimacs()
    nvars, ncl, _clauses = parse_dimacs(text)
    corrupted = text.replace(
        f"p cnf {nvars} {ncl}", f"p cnf {nvars} {ncl + 1}", 1
    )
    if corrupted == text:
        raise SystemExit("NEGATIVE control setup FAILED: header substitution missed")
    try:
        parse_dimacs(corrupted)
    except DimacsError as exc:
        print(f"NEGATIVE control: corrupted header clause count correctly refused ({exc})")
        return
    raise SystemExit(
        "NEGATIVE control FAILED: a header/body clause-count mismatch was silently accepted"
    )


if __name__ == "__main__":
    run_positive_control()
    run_negative_control()
    print("roundtrip_control: PASS")
    sys.exit(0)
