#!/bin/bash
# Re-runnable verification of the six published witnesses for A398173 a(15)-a(20).
# Inputs retained alongside; run from repo root.  Reports a POSITIVE result per
# witness and a NEGATIVE control, because a checker that cannot fail proves nothing.
# Self-contained: the USF/balanced check (rep_counts/unique_sums/is_usf/is_balanced)
# is inlined below so this script has no dependency outside this directory.
set -u
D=provenance/witness-recheck-2026-08-18
echo "== POSITIVE: each published witness must verify =="
python3 - "$D/witnesses.json" <<'PY'
import json,sys

def rep_counts(A, p):
    A = sorted(set(a % p for a in A))
    cnt = {}
    for i, a in enumerate(A):
        for b in A[i:]:
            s = (a + b) % p
            cnt[s] = cnt.get(s, 0) + 1
    return cnt

def unique_sums(A, p):
    return sorted(s for s, c in rep_counts(A, p).items() if c == 1)

def is_usf(A, p):
    return len(A) >= 2 and not unique_sums(A, p)

def is_balanced(A, p):
    S = set(a % p for a in A)
    for a in S:
        if not any((2 * a - b) % p in S and (2 * a - b) % p != b for b in S):
            return False
    return True

w = json.load(open(sys.argv[1]))
for k in sorted(w, key=int):
    v = w[k]; A = v['witness']; p = v['p']
    out = f"USF: {is_usf(A, p)} balanced: {is_balanced(A, p)} unique sums: {unique_sums(A, p)}"
    print(f"  a({v['n']}) p={p:>3} size={v['claimed_size']}: {out}")
PY
echo "== NEGATIVE CONTROL: a perturbed witness must FAIL =="
python3 - "$D/witnesses.json" <<'PY'
import json,sys

def rep_counts(A, p):
    A = sorted(set(a % p for a in A))
    cnt = {}
    for i, a in enumerate(A):
        for b in A[i:]:
            s = (a + b) % p
            cnt[s] = cnt.get(s, 0) + 1
    return cnt

def unique_sums(A, p):
    return sorted(s for s, c in rep_counts(A, p).items() if c == 1)

def is_usf(A, p):
    return len(A) >= 2 and not unique_sums(A, p)

def is_balanced(A, p):
    S = set(a % p for a in A)
    for a in S:
        if not any((2 * a - b) % p in S and (2 * a - b) % p != b for b in S):
            return False
    return True

w = json.load(open(sys.argv[1]))['15']
A = list(w['witness']); A[-1] = (A[-1] + 1) % w['p']
out = f"USF: {is_usf(A, w['p'])} balanced: {is_balanced(A, w['p'])} unique sums: {unique_sums(A, w['p'])}"
print(f"  p={w['p']} perturbed: {out}")
print("  CONTROL FIRED" if "USF: False" in out else "  *** CONTROL DID NOT FIRE -- table above is meaningless ***")
PY
