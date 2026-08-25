#!/usr/bin/env python3
"""k = p property test for the pinned production encoder.

Background. Z/pZ itself is unique-sum-free: every element of the group is in A, so every
sum has p unordered representations, never one. An encoder asked for a unique-sum-free
set of size k = p therefore has exactly one model (everything in) and must say SAT.
Forcing any single element out of A must then flip the verdict to UNSAT.

This corner is invisible to differential tests between two encoders and to replays of
UNSAT cubes, because both encoders can carry the same blind spot. Pawel Kwaczynski found
a sign error in his own symmetry breaker this way in August 2026: the formula for k = p
came back UNSAT although Z/pZ is unique-sum-free. The pinned encoder here has no symmetry
breaker, so it never had that defect, but nothing tested the boundary either. This does.

For each prime p in the list:
  POSITIVE  encode(p, p) must be SAT (kissat exit code 10, "s SATISFIABLE").
  NEGATIVE  the same CNF plus the unit clause "-1 0" (element 0 forced out of A; the
            pinned encoder puts membership of element i on variable i + 1) must be UNSAT
            (kissat exit code 20, "s UNSATISFIABLE"). A control that cannot flip is not a
            control.

Usage:  python3 kp_property_test.py [--kissat PATH] [--primes 7,13]
Exit status 0 only if every positive and every negative control passes.
"""
import argparse
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
ENCODER = HERE / "usf_encode_pinned.py"


def run(cmd):
    proc = subprocess.run(cmd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def verdict(output, rc):
    line = next((l for l in output.splitlines() if l.startswith("s ")), f"rc={rc}")
    return line.strip()


def add_unit_clause(cnf_text, literal):
    """Append one unit clause and bump the clause count in the DIMACS header."""
    out = []
    bumped = False
    for line in cnf_text.splitlines():
        if line.startswith("p cnf") and not bumped:
            _, _, nvars, nclauses = line.split()
            out.append(f"p cnf {nvars} {int(nclauses) + 1}")
            bumped = True
        else:
            out.append(line)
    if not bumped:
        raise SystemExit("no DIMACS header found")
    out.append(f"{literal} 0")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kissat", default=shutil.which("kissat"), help="path to kissat")
    ap.add_argument("--primes", default="7,13", help="comma-separated odd primes")
    args = ap.parse_args()
    if not args.kissat:
        raise SystemExit("kissat not found; pass --kissat PATH")
    primes = [int(x) for x in args.primes.split(",")]
    ok_all = True
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        for p in primes:
            rc, cnf = run([sys.executable, str(ENCODER), str(p), str(p)])
            if rc != 0 or "p cnf" not in cnf:
                print(f"p={p}: encoder failed (rc={rc})")
                ok_all = False
                continue
            pos = tmp / f"p{p}_pos.cnf"
            pos.write_text(cnf)
            rc_pos, out_pos = run([args.kissat, "-q", str(pos)])
            pos_ok = rc_pos == 10 and "s SATISFIABLE" in out_pos
            print(f"p={p} POSITIVE k=p must be SAT:   {verdict(out_pos, rc_pos)}  {'PASS' if pos_ok else 'FAIL'}")

            neg = tmp / f"p{p}_neg.cnf"
            neg.write_text(add_unit_clause(cnf, -1))
            rc_neg, out_neg = run([args.kissat, "-q", str(neg)])
            neg_ok = rc_neg == 20 and "s UNSATISFIABLE" in out_neg
            print(f"p={p} NEGATIVE 0 forced out, UNSAT: {verdict(out_neg, rc_neg)}  {'PASS' if neg_ok else 'FAIL'}")
            ok_all = ok_all and pos_ok and neg_ok
    print("ALL PASS" if ok_all else "FAILURE")
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
