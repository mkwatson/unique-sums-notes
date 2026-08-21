#!/usr/bin/env python3
"""Validate CENSSCHEMA schema-1 output rows using exact integer arithmetic."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
from typing import Iterator, Sequence


CONVENTION = 'ordered pairs; R_A(s) is never 1 or 2'


class ValidationError(ValueError):
  """A schema or mathematical validation failure."""


def integer_partitions(total: int, minimum: int = 1) -> Iterator[tuple[int, ...]]:
  if total == 0:
    yield ()
  for first in range(minimum, total + 1):
    for tail in integer_partitions(total - first, first):
      yield (first,) + tail


def prime_factorization(value: int) -> dict[int, int]:
  factors: dict[int, int] = {}
  divisor = 2
  remainder = value
  while divisor * divisor <= remainder:
    while remainder % divisor == 0:
      factors[divisor] = factors.get(divisor, 0) + 1
      remainder //= divisor
    divisor += 1
  if remainder > 1:
    factors[remainder] = 1
  return factors


def invariant_factor_groups(order: int) -> list[tuple[int, ...]]:
  choices = [
    [tuple(prime**part for part in partition) for partition in integer_partitions(exponent)]
    for prime, exponent in sorted(prime_factorization(order).items())
  ]
  groups: set[tuple[int, ...]] = set()
  for primary in itertools.product(*choices):
    rank = max(len(component) for component in primary)
    padded = [(1,) * (rank - len(component)) + component for component in primary]
    groups.add(tuple(math.prod(component[i] for component in padded) for i in range(rank)))
  return sorted(groups, key=lambda group: (len(group), group))


def encode(coordinates: Sequence[int], moduli: Sequence[int]) -> int:
  if len(coordinates) != len(moduli):
    raise ValidationError('coordinate rank differs from moduli rank')
  value = 0
  for coordinate, modulus in zip(coordinates, moduli, strict=True):
    if not 0 <= coordinate < modulus:
      raise ValidationError('coordinate outside canonical range')
    value = value * modulus + coordinate
  return value


def decode(value: int, moduli: Sequence[int]) -> tuple[int, ...]:
  order = math.prod(moduli)
  if not 0 <= value < order:
    raise ValidationError('element outside group range')
  coordinates: list[int] = []
  remainder = value
  for modulus in reversed(moduli):
    coordinates.append(remainder % modulus)
    remainder //= modulus
  return tuple(reversed(coordinates))


def add(left: int, right: int, moduli: Sequence[int]) -> int:
  left_coordinates = decode(left, moduli)
  right_coordinates = decode(right, moduli)
  return encode(
    tuple((a + b) % modulus for a, b, modulus in zip(left_coordinates, right_coordinates, moduli, strict=True)),
    moduli,
  )


def ordered_counts(witness: Sequence[int], moduli: Sequence[int]) -> tuple[int, ...]:
  counts = [0] * math.prod(moduli)
  for left in witness:
    for right in witness:
      counts[add(left, right, moduli)] += 1
  return tuple(counts)


def validate_certificate_family(lower: object) -> None:
  if not isinstance(lower, dict) or lower.get('status') != 'UNSAT':
    raise ValidationError('lower must be an UNSAT object')
  if lower.get('proof_verified') is not True or lower.get('witness') is not None:
    raise ValidationError('lower proof must be verified and have null witness')
  if not isinstance(lower.get('formula'), str):
    raise ValidationError('lower formula path is required')
  certificates = lower.get('certificates')
  if not isinstance(certificates, list) or not certificates:
    raise ValidationError('lower certificate family must be nonempty')
  for certificate in certificates:
    if not isinstance(certificate, dict):
      raise ValidationError('certificate entry must be an object')
    required = ('path', 'sha256', 'checker', 'checker_result')
    if any(not isinstance(certificate.get(key), str) for key in required):
      raise ValidationError('certificate entry lacks replay metadata')


def validate_row(row: object) -> None:
  if not isinstance(row, dict):
    raise ValidationError('row must be an object')
  moduli_value = row.get('moduli')
  if not isinstance(moduli_value, list) or not moduli_value or any(type(n) is not int or n < 2 for n in moduli_value):
    raise ValidationError('moduli must be nonempty integers >= 2')
  moduli = tuple(moduli_value)
  if any(right % left != 0 for left, right in itertools.pairwise(moduli)):
    raise ValidationError('moduli are not invariant factors')
  order = math.prod(moduli)
  expected_name = 'x'.join(f'C{modulus}' for modulus in moduli)
  if row.get('order') != order or row.get('group') != expected_name:
    raise ValidationError('group name/order does not match moduli')
  for element in range(order):
    if encode(decode(element, moduli), moduli) != element:
      raise ValidationError('element encode/decode round trip failed')
  for coordinates in itertools.product(*(range(modulus) for modulus in moduli)):
    if decode(encode(coordinates, moduli), moduli) != coordinates:
      raise ValidationError('coordinate decode/encode round trip failed')

  minimum = row.get('m')
  witness_value = row.get('witness')
  if minimum is None:
    if witness_value is not None or row.get('lower_bound') != order:
      raise ValidationError('nonexistence row requires null witness and lower_bound=order')
  else:
    if type(minimum) is not int or minimum < 1:
      raise ValidationError('m must be a positive integer or null')
    if not isinstance(witness_value, list) or len(witness_value) != minimum:
      raise ValidationError('witness length differs from m')
    if any(type(element) is not int or not 0 <= element < order for element in witness_value):
      raise ValidationError('witness contains an out-of-range element')
    if len(set(witness_value)) != len(witness_value):
      raise ValidationError('witness is not a set')
    bad = [(total, count) for total, count in enumerate(ordered_counts(witness_value, moduli)) if count in (1, 2)]
    if bad:
      raise ValidationError(f'wrong predicate: ordered representation fibres of size 1 or 2: {bad}')
    if row.get('lower_bound') != minimum - 1:
      raise ValidationError('lower_bound must equal m-1')
    upper = row.get('upper')
    if not isinstance(upper, dict) or upper.get('status') != 'SAT' or upper.get('witness') != witness_value:
      raise ValidationError('upper SAT model must decode to the stored witness')
    membership = upper.get('model_membership')
    if (
      not isinstance(membership, list)
      or len(membership) != order
      or any(type(selected) is not bool for selected in membership)
    ):
      raise ValidationError('upper model_membership must be one Boolean per element')
    decoded_witness = [element for element, selected in enumerate(membership) if selected]
    encoded_membership = [element in set(witness_value) for element in range(order)]
    if decoded_witness != witness_value:
      raise ValidationError('model-to-witness decoding does not match stored witness')
    if encoded_membership != membership:
      raise ValidationError('witness-to-model encoding does not match stored membership')

  lower = row.get('lower')
  validate_certificate_family(lower)
  assert isinstance(lower, dict)
  if lower.get('bound') != row.get('lower_bound'):
    raise ValidationError('lower certificate bound differs from row lower_bound')
  if row.get('tier') != 'EXACT COMPUTATION':
    raise ValidationError('tier must be EXACT COMPUTATION for this package')


def validate_document(document: object) -> int:
  if not isinstance(document, dict):
    raise ValidationError('document must be an object')
  if document.get('schema') != 1 or document.get('convention') != CONVENTION:
    raise ValidationError('wrong schema or predicate convention')
  results = document.get('results')
  if not isinstance(results, list) or document.get('group_count') != len(results):
    raise ValidationError('results/group_count mismatch')
  keys: list[tuple[int, int, tuple[int, ...]]] = []
  for row in results:
    validate_row(row)
    assert isinstance(row, dict) and isinstance(row['moduli'], list)
    moduli = tuple(row['moduli'])
    keys.append((row['order'], len(moduli), moduli))
  if keys != sorted(keys) or len(set(keys)) != len(keys):
    raise ValidationError('results are not unique and canonically ordered')
  return len(results)


def sha256(path: Path) -> str:
  digest = hashlib.sha256()
  with path.open('rb') as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b''):
      digest.update(block)
  return digest.hexdigest()


def main() -> int:
  parser = argparse.ArgumentParser()
  parser.add_argument('json_file', type=Path)
  arguments = parser.parse_args()
  try:
    document = json.loads(arguments.json_file.read_text(encoding='utf-8'))
    count = validate_document(document)
  except (OSError, json.JSONDecodeError, ValidationError) as error:
    print(f'REJECT: {error}')
    return 1
  print(f'ACCEPT: {count} row(s); exact ordered-predicate recount passed')
  return 0


if __name__ == '__main__':
  raise SystemExit(main())
