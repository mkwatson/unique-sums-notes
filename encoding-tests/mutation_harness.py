#!/usr/bin/env python3
"""Systematic mutation testing for the pinned production USF CNF encoder.

This is exhaustive differential testing on finite instances, not a proof.  The
unmutated local implementation must first match usf_encode_pinned.py exactly,
clause-for-clause.  Each mutant is then compared with an independent brute-force
USF oracle after existentially quantifying the encoder's auxiliary variables.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Protocol

from pysat.solvers import Cadical195, Minisat22

Clause = tuple[int, ...]


class ProductionCnf(Protocol):
  n: int
  clauses: list[list[int]]


@dataclass(frozen=True)
class Mutation:
  identifier: str
  category: str
  description: str
  before: str
  after: str


MUTATIONS = (
  Mutation('D01', 'clause deletion', 'delete the x_0 pin unit clause', 'cnf.add(x(0))', '<deleted>'),
  Mutation('D02', 'clause deletion', 'delete the x_1 pin unit clause', 'cnf.add(x(1))', '<deleted>'),
  Mutation('D03', 'clause deletion', 'delete every y -> x_a clause', 'cnf.add(-y, x(a))', '<deleted>'),
  Mutation('D04', 'clause deletion', 'delete every y -> x_b clause', 'cnf.add(-y, x(b))', '<deleted>'),
  Mutation('D05', 'clause deletion', 'delete every (x_a and x_b) -> y clause', 'cnf.add(-x(a), -x(b), y)', '<deleted>'),
  Mutation('D06', 'clause deletion', 'delete the complete R=1-forbidding clause family', 'cnf.add(-x(h), *ys)', '<deleted>'),
  Mutation('D07', 'clause deletion', 'delete the complete R=2-forbidding clause family', 'for j, yj in enumerate(ys): cnf.add(...)', '<deleted>'),
  Mutation('D08', 'clause deletion', 'delete the upper cardinality-counter clause family', 'seq_counter_atmost(cnf, mem, k)', '<deleted>'),
  Mutation('D09', 'clause deletion', 'delete the lower cardinality-counter clause family', 'seq_counter_atmost(cnf, [-v for v in mem], p - k)', '<deleted>'),
  Mutation('L01', 'literal flip', 'flip -y in the first y -> x_a clause', '(-y, x(a))', '(y, x(a))'),
  Mutation('L02', 'literal flip', 'flip x_a in the first y -> x_a clause', '(-y, x(a))', '(-y, -x(a))'),
  Mutation('L03', 'literal flip', 'flip -y in the first y -> x_b clause', '(-y, x(b))', '(y, x(b))'),
  Mutation('L04', 'literal flip', 'flip x_b in the first y -> x_b clause', '(-y, x(b))', '(-y, -x(b))'),
  Mutation('L05', 'literal flip', 'flip -x_a in the first endpoints -> y clause', '(-x(a), -x(b), y)', '(x(a), -x(b), y)'),
  Mutation('L06', 'literal flip', 'flip -x_b in the first endpoints -> y clause', '(-x(a), -x(b), y)', '(-x(a), x(b), y)'),
  Mutation('L07', 'literal flip', 'flip y in the first endpoints -> y clause', '(-x(a), -x(b), y)', '(-x(a), -x(b), -y)'),
  Mutation('L08', 'literal flip', 'flip -x_h in the first R=1 clause', '(-x(h), *ys)', '(x(h), *ys)'),
  Mutation('L09', 'literal flip', 'flip x_h in the first R=2 clause', '(x(h), -yj, *others)', '(-x(h), -yj, *others)'),
  Mutation('L10', 'literal flip', 'flip -y_j in the first R=2 clause', '(x(h), -yj, *others)', '(x(h), yj, *others)'),
  Mutation('B01', 'bound off-by-one', 'raise the upper cardinality bound by one', 'atmost(mem, k)', 'atmost(mem, k + 1)'),
  Mutation('B02', 'bound off-by-one', 'lower the upper cardinality bound by one', 'atmost(mem, k)', 'atmost(mem, k - 1)'),
  Mutation('B03', 'bound off-by-one', 'raise the complement cardinality bound by one', 'atmost(not mem, p - k)', 'atmost(not mem, p - k + 1)'),
  Mutation('B04', 'bound off-by-one', 'lower the complement cardinality bound by one', 'atmost(not mem, p - k)', 'atmost(not mem, p - k - 1)'),
  Mutation('B05', 'bound off-by-one', 'omit the final sum fibre', 'for s in range(p)', 'for s in range(p - 1)'),
  Mutation('B06', 'bound off-by-one', 'omit the final row of the upper sequential counter', 'for i in range(1, n)', 'for i in range(1, n - 1)'),
  Mutation('B07', 'bound off-by-one', 'omit the final row of the lower sequential counter', 'for i in range(1, n)', 'for i in range(1, n - 1)'),
  Mutation('C01', 'comparator swap', 'invert the diagonal-pair skip test', 'if a == b: continue', 'if a != b: continue'),
  Mutation('C02', 'comparator swap', 'replace diagonal equality by a < b in the skip test', 'if a == b: continue', 'if a < b: continue'),
  Mutation('C03', 'comparator swap', 'replace diagonal equality by a > b in the skip test', 'if a == b: continue', 'if a > b: continue'),
  Mutation('C04', 'comparator swap', 'invert the seen-pair membership test', 'if key in seen: continue', 'if key not in seen: continue'),
  Mutation('C05', 'comparator swap', 'retain only y_j, rather than every other y, in R=2 clauses', 'if m != j', 'if m == j'),
  Mutation('C06', 'comparator swap', 'retain only later y variables in R=2 clauses', 'if m != j', 'if m > j'),
  Mutation('C07', 'comparator swap', 'change the pin guard from k >= 2 to k > 2', 'if k >= 2', 'if k > 2'),
  Mutation('C08', 'comparator swap', 'change the pin guard from k >= 2 to k <= 2', 'if k >= 2', 'if k <= 2'),
)

MUTATION_BY_ID = {mutation.identifier: mutation for mutation in MUTATIONS}


class Cnf:
  def __init__(self, nvars: int) -> None:
    self.n = nvars
    self.clauses: list[Clause] = []

  def new(self) -> int:
    self.n += 1
    return self.n

  def add(self, *literals: int) -> None:
    self.clauses.append(tuple(literals))


class MutantEncoder:
  def __init__(self, mutation_id: str | None) -> None:
    self.mutation_id = mutation_id
    self.applications = 0

  def active(self, identifier: str) -> bool:
    if self.mutation_id == identifier:
      self.applications += 1
      return True
    return False

  def diagonal_skipped(self, left: int, right: int) -> bool:
    if self.active('C01'):
      return left != right
    if self.active('C02'):
      return left < right
    if self.active('C03'):
      return left > right
    return left == right

  def pair_seen(self, key: tuple[int, int], seen: set[tuple[int, int]]) -> bool:
    if self.active('C04'):
      return key not in seen
    return key in seen

  def seq_counter_atmost(self, cnf: Cnf, literals: list[int], bound: int, site: str) -> None:
    size = len(literals)
    if bound < 0:
      cnf.add()
      return
    if bound >= size:
      return
    if bound == 0:
      for literal in literals:
        cnf.add(-literal)
      return
    rows = [[cnf.new() for _ in range(bound)] for _ in range(size)]
    cnf.add(-literals[0], rows[0][0])
    for column in range(1, bound):
      cnf.add(-rows[0][column])
    stop = size
    if site == 'upper' and self.active('B06'):
      stop = size - 1
    if site == 'lower' and self.active('B07'):
      stop = size - 1
    for row in range(1, stop):
      cnf.add(-literals[row], rows[row][0])
      cnf.add(-rows[row - 1][0], rows[row][0])
      for column in range(1, bound):
        cnf.add(-literals[row], -rows[row - 1][column - 1], rows[row][column])
        cnf.add(-rows[row - 1][column], rows[row][column])
      cnf.add(-literals[row], -rows[row - 1][bound - 1])

  def encode(self, p: int, k: int) -> Cnf:
    if p % 2 != 1:
      raise ValueError('odd modulus required')
    cnf = Cnf(p)
    member = lambda value: value + 1
    inverse_two = pow(2, p - 2, p)
    sum_stop = p - 1 if self.active('B05') else p
    first_pair = True
    first_r1 = True
    first_r2 = True
    for total in range(sum_stop):
      half = total * inverse_two % p
      pairs: list[tuple[int, int]] = []
      seen: set[tuple[int, int]] = set()
      for left in range(p):
        right = (total - left) % p
        if self.diagonal_skipped(left, right):
          continue
        key = (min(left, right), max(left, right))
        if self.pair_seen(key, seen):
          continue
        seen.add(key)
        pairs.append(key)
      pair_variables: list[int] = []
      for left, right in pairs:
        pair_variable = cnf.new()
        left_clause = (-pair_variable, member(left))
        right_clause = (-pair_variable, member(right))
        forward_clause = (-member(left), -member(right), pair_variable)
        if first_pair and self.active('L01'):
          left_clause = (pair_variable, member(left))
        if first_pair and self.active('L02'):
          left_clause = (-pair_variable, -member(left))
        if first_pair and self.active('L03'):
          right_clause = (pair_variable, member(right))
        if first_pair and self.active('L04'):
          right_clause = (-pair_variable, -member(right))
        if first_pair and self.active('L05'):
          forward_clause = (member(left), -member(right), pair_variable)
        if first_pair and self.active('L06'):
          forward_clause = (-member(left), member(right), pair_variable)
        if first_pair and self.active('L07'):
          forward_clause = (-member(left), -member(right), -pair_variable)
        if not self.active('D03'):
          cnf.add(*left_clause)
        if not self.active('D04'):
          cnf.add(*right_clause)
        if not self.active('D05'):
          cnf.add(*forward_clause)
        pair_variables.append(pair_variable)
        first_pair = False
      r1_clause = (-member(half), *pair_variables)
      if first_r1 and self.active('L08'):
        r1_clause = (member(half), *pair_variables)
      if not self.active('D06'):
        cnf.add(*r1_clause)
      first_r1 = False
      for index, pair_variable in enumerate(pair_variables):
        if self.active('C05'):
          others = [pair_variables[position] for position in range(len(pair_variables)) if position == index]
        elif self.active('C06'):
          others = [pair_variables[position] for position in range(len(pair_variables)) if position > index]
        else:
          others = [pair_variables[position] for position in range(len(pair_variables)) if position != index]
        r2_clause = (member(half), -pair_variable, *others)
        if first_r2 and self.active('L09'):
          r2_clause = (-member(half), -pair_variable, *others)
        if first_r2 and self.active('L10'):
          r2_clause = (member(half), pair_variable, *others)
        if not self.active('D07'):
          cnf.add(*r2_clause)
        first_r2 = False

    membership = [member(value) for value in range(p)]
    upper_bound = k
    lower_bound = p - k
    if self.active('B01'):
      upper_bound += 1
    if self.active('B02'):
      upper_bound -= 1
    if self.active('B03'):
      lower_bound += 1
    if self.active('B04'):
      lower_bound -= 1
    if not self.active('D08'):
      self.seq_counter_atmost(cnf, membership, upper_bound, 'upper')
    if not self.active('D09'):
      self.seq_counter_atmost(cnf, [-variable for variable in membership], lower_bound, 'lower')

    pin_guard = k >= 2
    if self.active('C07'):
      pin_guard = k > 2
    if self.active('C08'):
      pin_guard = k <= 2
    if pin_guard:
      if not self.active('D01'):
        cnf.add(member(0))
      if not self.active('D02'):
        cnf.add(member(1))
    return cnf


def primes_through(limit: int) -> tuple[int, ...]:
  return tuple(
    candidate for candidate in range(3, limit + 1, 2)
    if all(candidate % divisor for divisor in range(2, int(candidate**0.5) + 1))
  )


def selected_from_mask(mask: int, p: int) -> tuple[int, ...]:
  return tuple(value for value in range(p) if mask & (1 << value))


def oracle_usf(p: int, selected: tuple[int, ...]) -> bool:
  counts = [0] * p
  for left in selected:
    for right in selected:
      counts[(left + right) % p] += 1
  return all(count not in (1, 2) for count in counts)


def oracle_accepts(p: int, k: int, mask: int) -> bool:
  selected = selected_from_mask(mask, p)
  return len(selected) == k and 0 in selected and 1 in selected and oracle_usf(p, selected)


def solver_accepts(solver: Minisat22 | Cadical195, p: int, mask: int) -> bool:
  assumptions = [value + 1 if mask & (1 << value) else -(value + 1) for value in range(p)]
  return solver.solve(assumptions=assumptions)


def first_semantic_difference(
  cnf: Cnf,
  p: int,
  k: int,
  solver_class: type[Minisat22] | type[Cadical195],
) -> dict[str, object] | None:
  with solver_class() as solver:
    for clause in cnf.clauses:
      solver.add_clause(list(clause))
    for mask in range(1 << p):
      actual = solver_accepts(solver, p, mask)
      expected = oracle_accepts(p, k, mask)
      if actual != expected:
        return {
          'p': p,
          'k': k,
          'set': list(selected_from_mask(mask, p)),
          'expected': expected,
          'actual': actual,
          'direction': 'false SAT / too permissive' if actual else 'false UNSAT / too restrictive',
        }
  return None


def load_module(path: Path) -> ModuleType:
  spec = importlib.util.spec_from_file_location('usf_encode_pinned_under_test', path)
  if spec is None or spec.loader is None:
    raise RuntimeError(f'cannot load production encoder: {path}')
  module = importlib.util.module_from_spec(spec)
  spec.loader.exec_module(module)
  return module


def source_sha256(path: Path) -> str:
  return hashlib.sha256(path.read_bytes()).hexdigest()


def cnf_sha256(cnf: Cnf) -> str:
  payload = json.dumps({'n': cnf.n, 'clauses': cnf.clauses}, separators=(',', ':'))
  return hashlib.sha256(payload.encode('ascii')).hexdigest()


def suite_signature(encoder: MutantEncoder, cases: tuple[tuple[int, int], ...]) -> str:
  digest = hashlib.sha256()
  for p, k in cases:
    digest.update(f'{p}:{k}:'.encode('ascii'))
    digest.update(cnf_sha256(encoder.encode(p, k)).encode('ascii'))
  return digest.hexdigest()


def default_encoder_path() -> Path:
  here = Path(__file__).resolve()
  candidate = here.parent / 'usf_encode_pinned.py'
  if candidate.exists():
    return candidate
  raise FileNotFoundError('could not locate usf_encode_pinned.py beside this script')


def run(limit: int, encoder_path: Path, output: Path) -> dict[str, object]:
  started = time.monotonic()
  primes = primes_through(limit)
  if not primes:
    raise ValueError('limit must include at least one odd prime')
  cases = tuple((p, k) for p in primes for k in range(2, p + 1))
  production = load_module(encoder_path)
  production_encode = getattr(production, 'encode', None)
  if not callable(production_encode):
    raise RuntimeError('production encoder has no callable encode')

  baseline = MutantEncoder(None)
  baseline_cases: list[dict[str, object]] = []
  for p, k in cases:
    local_cnf = baseline.encode(p, k)
    production_cnf: ProductionCnf = production_encode(p, k)
    production_clauses = [tuple(clause) for clause in production_cnf.clauses]
    if local_cnf.n != production_cnf.n or local_cnf.clauses != production_clauses:
      raise AssertionError(f'unmutated clone differs from production at p={p}, k={k}')
    minisat_difference = first_semantic_difference(local_cnf, p, k, Minisat22)
    cadical_difference = first_semantic_difference(local_cnf, p, k, Cadical195)
    if minisat_difference != cadical_difference:
      raise AssertionError(f'baseline SAT engines disagree at p={p}, k={k}')
    if minisat_difference is not None:
      raise AssertionError(f'production baseline differs from oracle: {minisat_difference}')
    expected_count = sum(oracle_accepts(p, k, mask) for mask in range(1 << p))
    baseline_cases.append({
      'p': p,
      'k': k,
      'projected_satisfying_assignments': expected_count,
      'cnf_sha256': cnf_sha256(local_cnf),
    })

  baseline_signature = suite_signature(MutantEncoder(None), cases)
  signatures: dict[str, str] = {}
  results: list[dict[str, object]] = []
  for mutation in MUTATIONS:
    signature_encoder = MutantEncoder(mutation.identifier)
    signature = suite_signature(signature_encoder, cases)
    if signature == baseline_signature:
      raise AssertionError(f'{mutation.identifier} never changes generated CNF')
    if signature in signatures:
      raise AssertionError(f'{mutation.identifier} duplicates mutant {signatures[signature]} over the test suite')
    signatures[signature] = mutation.identifier

    caught_by: dict[str, object] | None = None
    total_applications = 0
    first_cnf_difference: dict[str, int] | None = None
    for p, k in cases:
      mutant_encoder = MutantEncoder(mutation.identifier)
      mutant_cnf = mutant_encoder.encode(p, k)
      total_applications += mutant_encoder.applications
      baseline_cnf = MutantEncoder(None).encode(p, k)
      if first_cnf_difference is None and cnf_sha256(mutant_cnf) != cnf_sha256(baseline_cnf):
        first_cnf_difference = {'p': p, 'k': k}
      minisat_difference = first_semantic_difference(mutant_cnf, p, k, Minisat22)
      cadical_difference = first_semantic_difference(mutant_cnf, p, k, Cadical195)
      if minisat_difference != cadical_difference:
        raise AssertionError(f'{mutation.identifier}: SAT engines disagree at p={p}, k={k}')
      if minisat_difference is not None:
        caught_by = minisat_difference
        break
    if total_applications == 0:
      raise AssertionError(f'{mutation.identifier} mutation site was never exercised')
    results.append({
      **asdict(mutation),
      'verdict': 'CAUGHT' if caught_by is not None else 'SURVIVED',
      'caught_by': caught_by,
      'first_cnf_difference': first_cnf_difference,
      'suite_cnf_sha256': signature,
    })

  category_counts: dict[str, int] = {}
  for mutation in MUTATIONS:
    category_counts[mutation.category] = category_counts.get(mutation.category, 0) + 1
  caught = sum(result['verdict'] == 'CAUGHT' for result in results)
  result = {
    'tier': 'TESTED, SINGLE-ARM, NOT KERNEL-CERTIFIED',
    'method': 'exhaustive projected-satisfying-assignment differential test with independent Minisat22 and CaDiCaL 1.9.5 engines against a brute-force USF oracle',
    'production_encoder': encoder_path.name,
    'production_encoder_sha256': source_sha256(encoder_path),
    'limit': limit,
    'primes': list(primes),
    'sizes': 'every 2 <= k <= p',
    'baseline_cases': baseline_cases,
    'baseline_suite_cnf_sha256': baseline_signature,
    'baseline_clause_identity': 'PASS',
    'baseline_oracle_agreement': 'PASS',
    'mutation_count': len(MUTATIONS),
    'category_counts': category_counts,
    'caught': caught,
    'survived': len(MUTATIONS) - caught,
    'all_mutant_cnf_signatures_distinct': True,
    'mutations': results,
    'elapsed_seconds': round(time.monotonic() - started, 3),
  }
  output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
  return result


def main() -> int:
  parser = argparse.ArgumentParser()
  parser.add_argument('--limit', type=int, default=13)
  parser.add_argument('--encoder', type=Path, default=None)
  parser.add_argument('--output', type=Path, default=Path(__file__).with_name('mutation-harness-results.json'))
  args = parser.parse_args()
  encoder_path = args.encoder.resolve() if args.encoder is not None else default_encoder_path()
  result = run(args.limit, encoder_path, args.output.resolve())
  print(
    f"MUTATION HARNESS: {result['caught']}/{result['mutation_count']} caught, "
    f"{result['survived']} survived; baseline={result['baseline_oracle_agreement']}; "
    f"elapsed={result['elapsed_seconds']}s"
  )
  return 0 if result['survived'] == 0 else 1


if __name__ == '__main__':
  raise SystemExit(main())
