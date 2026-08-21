#!/usr/bin/env python3
"""Positive and wrong-predicate negative controls for CENSSCHEMA."""

from __future__ import annotations

from copy import deepcopy

from validator import CONVENTION, ValidationError, validate_document


HASH = '0' * 64


def row(witness: list[int], minimum: int) -> dict[str, object]:
  membership = [element in set(witness) for element in range(11)]
  return {
    'group': 'C11',
    'moduli': [11],
    'order': 11,
    'm': minimum,
    'witness': witness,
    'lower_bound': minimum - 1,
    'lower': {
      'status': 'UNSAT',
      'bound': minimum - 1,
      'formula': 'cert/C11/lower.cnf',
      'formula_sha256': HASH,
      'certificates': [{
        'path': 'cert/C11/lower.drat',
        'sha256': HASH,
        'checker': 'drat-trim',
        'checker_result': 's VERIFIED',
      }],
      'proof_verified': True,
      'witness': None,
    },
    'upper': {
      'status': 'SAT',
      'witness': witness,
      'model_membership': membership,
    },
    'tier': 'EXACT COMPUTATION',
  }


def document(result: dict[str, object]) -> dict[str, object]:
  return {
    'schema': 1,
    'convention': CONVENTION,
    'complete': True,
    'group_count': 1,
    'max_order_requested': 11,
    'results': [result],
    'stress_group_count': 0,
    'stress_results': [],
  }


def main() -> int:
  positive = document(row([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 11))
  assert validate_document(positive) == 1
  print('positive_controls_passed=1')

  false_gloss = document(row([0, 1, 2, 4, 7], 5))
  attempted = 1
  fired = 0
  try:
    validate_document(deepcopy(false_gloss))
  except ValidationError as error:
    fired += 1
    print(f'negative_control_rejection={error}')
  print(f'negative_controls_attempted={attempted}')
  print(f'negative_controls_fired={fired}')
  if fired != attempted:
    print('CONTROL FAILURE: wrong-predicate row was admitted')
    return 1
  print('PHASE 2 DONE: validator accepted the positive row and rejected the false-gloss row.')
  return 0


if __name__ == '__main__':
  raise SystemExit(main())
