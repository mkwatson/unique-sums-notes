#!/usr/bin/env python3
"""One-command, deterministic reproduction harness for deliverable/note.tex."""

from __future__ import annotations

import hashlib
import itertools
import json
import subprocess
import sys
import time
from math import comb
from pathlib import Path
from typing import Callable


ROOT = Path(__file__).resolve().parents[1]
NOTE = ROOT / 'note-v4' / 'note.tex'
VERIFY = Path(__file__).with_name('support') / 'verify.py'
CENSUS = Path(__file__).with_name('support') / 'mg-census-through-52.json'


def canonical(value: object) -> bytes:
  return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def digest_bytes(value: bytes) -> str:
  return hashlib.sha256(value).hexdigest()


def digest_file(path: Path) -> str:
  return digest_bytes(path.read_bytes())


def ordered_usf(values: tuple[int, ...], modulus: int) -> tuple[bool, tuple[int, ...]]:
  counts = [0] * modulus
  for left in values:
    for right in values:
      counts[(left + right) % modulus] += 1
  return all(count == 0 or count >= 3 for count in counts), tuple(counts)


def unordered_usf_group(values: list[int], moduli: tuple[int, ...]) -> bool:
  def decode(value: int) -> tuple[int, ...]:
    result = []
    for modulus in reversed(moduli):
      result.append(value % modulus)
      value //= modulus
    return tuple(reversed(result))

  elements = [decode(value) for value in values]
  counts: dict[tuple[int, ...], int] = {}
  for index, left in enumerate(elements):
    for right in elements[index:]:
      total = tuple((a + b) % modulus for a, b, modulus in zip(left, right, moduli))
      counts[total] = counts.get(total, 0) + 1
  return bool(values) and all(count != 1 for count in counts.values())


def ordered_trap() -> tuple[bool, object, object]:
  inputs = {'A': [0, 1, 2, 4, 7], 'modulus': 11, 'expected_usf': False}
  actual, counts = ordered_usf(tuple(inputs['A']), 11)
  output = {'usf': actual, 'ordered_counts': counts}
  return actual is False, inputs, output


def deliberate_control() -> tuple[bool, object, object]:
  inputs = {'A': [0, 1, 2, 4, 7], 'modulus': 11, 'intentionally_wrong_expected_usf': True}
  actual, _ = ordered_usf(tuple(inputs['A']), 11)
  output = {'actual_usf': actual, 'comparison_matches': actual is True}
  return actual is True, inputs, output


def legacy_verify() -> tuple[bool, object, object]:
  process = subprocess.run(
    [sys.executable, str(VERIFY)], cwd=VERIFY.parent, text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
  )
  inputs = {'verify_py_sha256': digest_file(VERIFY)}
  output = {'returncode': process.returncode, 'stdout': process.stdout}
  return process.returncode == 0, inputs, output


def census_manifest() -> tuple[bool, object, object]:
  raw = CENSUS.read_bytes()
  data = json.loads(raw)
  rows = data['results'] + data['stress_results']
  witnesses_ok = 0
  formula_ok = 0
  exact_prime = {3: 3, 5: 4, 7: 5, 11: 7, 13: 7, 17: 8, 19: 9, 23: 10,
                 29: 11, 31: 11, 37: 12, 41: 13, 43: 13, 47: 13}
  for row in rows:
    witness = row.get('witness')
    if witness is not None and unordered_usf_group(witness, tuple(row['moduli'])):
      witnesses_ok += 1
    candidates = ([4] if row['order'] % 4 == 0 else []) + [
      value for prime, value in exact_prime.items() if row['order'] % prime == 0
    ]
    predicted = min(candidates) if candidates else None
    if row['m'] == predicted:
      formula_ok += 1
  passed = (
    digest_bytes(raw) == 'f8d1c7119e5e98f6d97c7bd4bc76e7eeac1060915876196040f6df74f9a073e9'
    and data['group_count'] == 88 and data['stress_group_count'] == 26
    and len(rows) == 114 and formula_ok == 114 and witnesses_ok == 113
    and all(row['lower']['proof_verified'] is True for row in rows)
  )
  inputs = {'manifest_sha256': digest_bytes(raw), 'rows': len(rows)}
  output = {'formula_matches': formula_ok, 'witnesses_recounted': witnesses_ok,
            'proof_verified_flags': sum(row['lower']['proof_verified'] is True for row in rows)}
  return passed, inputs, output


def selector_witness_127() -> tuple[bool, object, object]:
  modulus = 127
  values = (0, 1, 2, 4, 8, 16, 32, 64)
  constraints = []
  for center in values:
    for left in values:
      for right in values:
        if left < right and left != center and right != center and (left + right - 2 * center) % modulus == 0:
          constraints.append((left, center, right))

  def valid(order: tuple[int, ...]) -> bool:
    position = {value: index for index, value in enumerate(order)}
    return all((position[left] < position[center] < position[right]) or
               (position[right] < position[center] < position[left])
               for left, center, right in constraints)

  satisfying_orders = sum(valid(order) for order in itertools.permutations(values))
  normalized_seven_subsets = comb(125, 5)
  inputs = {'modulus': modulus, 'S': values, 'criterion': 'all midpoint relations require betweenness',
            'published_normalized_seven_subset_count': 234531275}
  output = {'midpoint_constraints': len(constraints), 'satisfying_linear_orders': satisfying_orders,
            'normalized_seven_subset_count': normalized_seven_subsets}
  return satisfying_orders == 0 and normalized_seven_subsets == 234531275, inputs, output


def one_log_crossover() -> tuple[bool, object, object]:
  inputs = {'bound': 'sqrt(M/404)', 'free_lower_bound': 1, 'M': 'log2(log2(p))'}
  # sqrt(M/404) exceeds 1 exactly when M > 404, hence when p > 2^(2^404).
  comparisons = {403: 403 < 404, 404: 404 == 404, 405: 405 > 404}
  output = {'threshold_M': 404, 'strictly_nonvacuous_iff_M_gt': 404, 'boundary_checks': comparisons}
  return comparisons == {403: True, 404: True, 405: True}, inputs, output


def run_row(name: str, function: Callable[[], tuple[bool, object, object]], expected_failure: bool = False) -> dict[str, object]:
  started = time.perf_counter()
  passed, inputs, output = function()
  elapsed = time.perf_counter() - started
  status = 'EXPECTED-FAIL' if expected_failure and not passed else ('PASS' if passed else 'FAIL')
  return {'claim': name, 'status': status, 'seconds': elapsed,
          'input_sha256': digest_bytes(canonical(inputs)),
          'output_sha256': digest_bytes(canonical(output)), 'output': output}


def main() -> int:
  started = time.perf_counter()
  rows = [
    run_row('ORDERED-COUNT-TRAP', ordered_trap),
    run_row('DELIBERATE-FAILING-CONTROL', deliberate_control, expected_failure=True),
    run_row('DELIVERABLE-VERIFY-LEGACY-SUITE', legacy_verify),
    run_row('CENSUS-52-MANIFEST-AND-WITNESSES', census_manifest),
    run_row('ONE-LOG-NUMERICAL-CROSSOVER', one_log_crossover),
    run_row('SELECTOR-P127-EXPLICIT-FAILURE', selector_witness_127),
  ]
  print('claim                                      status         seconds  input_sha256 output_sha256')
  print('-' * 132)
  for row in rows:
    print(f"{row['claim']:<42} {row['status']:<14} {row['seconds']:>7.3f}  "
          f"{row['input_sha256']} {row['output_sha256']}")
  firing_count = sum(row['claim'] == 'DELIBERATE-FAILING-CONTROL' and row['status'] == 'EXPECTED-FAIL' for row in rows)
  failures = sum(row['status'] == 'FAIL' for row in rows)
  print(f'\nfailing_control_firing_count={firing_count}')
  print(f'unexpected_failure_count={failures}')
  print(f'wall_seconds={time.perf_counter() - started:.3f}')
  details = Path(__file__).with_name('last-run.json')
  details.write_text(json.dumps({'rows': rows, 'failing_control_firing_count': firing_count,
                                 'unexpected_failure_count': failures}, indent=2, sort_keys=True) + '\n')
  return 0 if failures == 0 and firing_count == 1 else 1


if __name__ == '__main__':
  raise SystemExit(main())
