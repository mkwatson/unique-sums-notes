#!/usr/bin/env python3
"""Differential TESTING for odd-prime USF encodings. This is not a proof."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import tempfile
import time
from collections.abc import Callable, Iterable, Sequence
from pathlib import Path

from ortools.sat.python import cp_model

Clause = tuple[int, ...]
MaskSet = frozenset[int]


def primes_through(limit: int) -> tuple[int, ...]:
  return tuple(
    n for n in range(3, limit + 1, 2)
    if all(n % divisor for divisor in range(2, int(n**0.5) + 1))
  )


def ordered_counts(p: int, selected: Iterable[int]) -> tuple[int, ...]:
  counts = [0] * p
  values = tuple(selected)
  for left in values:
    for right in values:
      counts[(left + right) % p] += 1
  return tuple(counts)


def oracle_usf(p: int, selected: Iterable[int]) -> bool:
  values = tuple(selected)
  return len(values) >= 2 and all(count not in (1, 2) for count in ordered_counts(p, values))


def oracle_by_size(p: int) -> dict[int, set[MaskSet]]:
  answer = {size: set() for size in range(2, p + 1)}
  for size in range(2, p + 1):
    for values in itertools.combinations(range(p), size):
      if oracle_usf(p, values):
        answer[size].add(frozenset(values))
  return answer


class DirectCnf:
  """Direct clauses: pair conjunctions, fibre support, and exact cardinality."""

  def __init__(self, p: int, k: int, mutation: str | None = None) -> None:
    self.p = p
    self.k = k
    self.mutation = mutation
    self.top = p
    self.clauses: list[Clause] = []
    self.pairs: dict[tuple[int, int], int] = {}
    self._build()

  def fresh(self) -> int:
    self.top += 1
    return self.top

  def _sum_index(self, left: int, right: int) -> int | None:
    raw = left + right
    if self.mutation == 'wrong-modulus':
      return raw % (self.p - 1)
    if self.mutation == 'ignore-wraparound':
      return raw if raw < self.p else None
    return raw % self.p

  def _build(self) -> None:
    fibres: list[list[int]] = [[] for _ in range(self.p)]
    for left in range(self.p):
      diagonal_sum = self._sum_index(left, left)
      if diagonal_sum is not None and self.mutation != 'drop-diagonals':
        fibres[diagonal_sum].append(left + 1)
      for right in range(left + 1, self.p):
        variable = self.fresh()
        self.pairs[(left, right)] = variable
        self.clauses.extend(((-(left + 1), -(right + 1), variable), (-variable, left + 1), (-variable, right + 1)))
        total = self._sum_index(left, right)
        if total is not None:
          fibres[total].append(variable)

    for fibre in fibres:
      if self.mutation == 'forbid-one-not-two':
        # Only diagonal singleton fibres are forbidden.
        diagonals = {2 * value % self.p: value + 1 for value in range(self.p)}
        for total, literal in diagonals.items():
          if literal in fibres[total]:
            others = tuple(item for item in fibres[total] if item != literal)
            self.clauses.append((-literal, *others))
      elif self.mutation == 'forbid-two-not-one':
        # Only singleton off-diagonal unordered representations are forbidden.
        membership = set(range(1, self.p + 1))
        for literal in fibre:
          if literal not in membership:
            self.clauses.append((-literal, *(item for item in fibre if item != literal)))
      else:
        for index, literal in enumerate(fibre):
          self.clauses.append((-literal, *fibre[:index], *fibre[index + 1 :]))

    target = self.k + 1 if self.mutation == 'cardinality-off-by-one' else self.k
    membership = tuple(range(1, self.p + 1))
    for chosen in itertools.combinations(membership, target + 1):
      self.clauses.append(tuple(-literal for literal in chosen))
    for absent in itertools.combinations(membership, self.p - target + 1):
      self.clauses.append(absent)

  def assignment(self, selected: MaskSet) -> set[int]:
    true_vars = {value + 1 for value in selected}
    true_vars.update(
      variable for (left, right), variable in self.pairs.items()
      if left in selected and right in selected
    )
    return true_vars

  def accepts(self, selected: MaskSet) -> bool:
    true_vars = self.assignment(selected)
    return all(any((literal > 0) == (abs(literal) in true_vars) for literal in clause) for clause in self.clauses)

  def dimacs(self) -> bytes:
    lines = [f'p cnf {self.top} {len(self.clauses)}']
    lines.extend(f"{' '.join(map(str, clause))} 0" for clause in self.clauses)
    return ('\n'.join(lines) + '\n').encode('ascii')


class SolutionCollector(cp_model.CpSolverSolutionCallback):
  def __init__(self, membership: Sequence[cp_model.IntVar]) -> None:
    super().__init__()
    self.membership = membership
    self.solutions: set[MaskSet] = set()

  def on_solution_callback(self) -> None:
    self.solutions.add(frozenset(index for index, variable in enumerate(self.membership) if self.value(variable)))


def cpsat_solutions(p: int, k: int) -> set[MaskSet]:
  """Independent formulation: integer fibre loads constrained to {0} union [2,...]."""
  model = cp_model.CpModel()
  membership = [model.new_bool_var(f'member_{value}') for value in range(p)]
  model.add(sum(membership) == k)
  fibres: list[list[cp_model.IntVar]] = [[] for _ in range(p)]
  for left in range(p):
    fibres[(2 * left) % p].append(membership[left])
  for left, right in itertools.combinations(range(p), 2):
    together = model.new_bool_var(f'together_{left}_{right}')
    model.add_multiplication_equality(together, (membership[left], membership[right]))
    fibres[(left + right) % p].append(together)
  for total, fibre in enumerate(fibres):
    load = model.new_int_var(0, len(fibre), f'load_{total}')
    model.add(load == sum(fibre))
    model.add_allowed_assignments((load,), ((0,), *tuple((value,) for value in range(2, len(fibre) + 1))))
  solver = cp_model.CpSolver()
  solver.parameters.enumerate_all_solutions = True
  solver.parameters.num_search_workers = 1
  collector = SolutionCollector(membership)
  status = solver.solve(model, collector)
  if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE):
    raise RuntimeError(f'CP-SAT did not complete at p={p}, k={k}: {solver.status_name(status)}')
  return collector.solutions


def decode_kissat(output: str, p: int) -> MaskSet:
  literals: dict[int, bool] = {}
  for line in output.splitlines():
    if line.startswith('v '):
      for token in line[2:].split():
        literal = int(token)
        if literal:
          literals[abs(literal)] = literal > 0
  if any(variable not in literals for variable in range(1, p + 1)):
    raise RuntimeError('kissat model omitted a membership variable')
  return frozenset(value for value in range(p) if literals[value + 1])


def verifier_accepts(verifier: Path, p: int, selected: MaskSet) -> bool:
  run = subprocess.run(
    ['python3', str(verifier), 'verify', str(p), ','.join(map(str, sorted(selected)))],
    check=False, capture_output=True, text=True,
  )
  return run.returncode == 0 and 'USF: True' in run.stdout


def digest_sets(sets: set[MaskSet]) -> str:
  payload = ';'.join(','.join(map(str, sorted(values))) for values in sorted(sets, key=lambda x: tuple(sorted(x))))
  return hashlib.sha256(payload.encode('ascii')).hexdigest()


def first_difference(actual: set[MaskSet], expected: set[MaskSet]) -> dict[str, list[int]] | None:
  extra = actual - expected
  missing = expected - actual
  if not extra and not missing:
    return None
  answer: dict[str, list[int]] = {}
  if extra:
    answer['extra'] = sorted(next(iter(extra)))
  if missing:
    answer['missing'] = sorted(next(iter(missing)))
  return answer


def run(limit: int, kissat: Path, verifier: Path, output: Path) -> None:
  started = time.monotonic()
  gloss = frozenset((0, 1, 2, 4, 7))
  even = frozenset((0, 1, 2, 3, 5, 6, 8))
  records: list[dict[str, object]] = []
  mutations = (
    'forbid-one-not-two', 'forbid-two-not-one', 'drop-diagonals',
    'cardinality-off-by-one', 'wrong-modulus', 'ignore-wraparound',
  )
  mutation_results: dict[str, dict[str, object]] = {
    name: {'detected': False, 'check': '', 'p': None, 'k': None, 'witness': None, 'direction': None}
    for name in mutations
  }
  model_decode_passes = 0
  witness_satisfies_passes = 0
  kissat_model_passes = 0
  primes = primes_through(limit)
  for p in primes:
    oracle = oracle_by_size(p)
    for k in range(2, p + 1):
      expected = oracle[k]
      direct = DirectCnf(p, k)
      direct_sets = {
        frozenset(values) for values in itertools.combinations(range(p), k)
        if direct.accepts(frozenset(values))
      }
      cp_sets = cpsat_solutions(p, k)
      direct_diff = first_difference(direct_sets, expected)
      cp_diff = first_difference(cp_sets, expected)
      mutual_diff = first_difference(direct_sets, cp_sets)
      if direct_diff or cp_diff or mutual_diff:
        failure = {'p': p, 'k': k, 'direct_vs_oracle': direct_diff, 'cpsat_vs_oracle': cp_diff, 'encoders': mutual_diff}
        output.write_text(json.dumps({'DISAGREEMENT': failure}, indent=2) + '\n', encoding='utf-8')
        raise AssertionError(f'encoding disagreement: {failure}')
      for selected in cp_sets:
        if not verifier_accepts(verifier, p, selected):
          raise AssertionError(f'model-decodes failed at p={p}, k={k}, A={sorted(selected)}')
        model_decode_passes += 1
      for selected in expected:
        if not direct.accepts(selected) or selected not in cp_sets:
          raise AssertionError(f'witness-satisfies failed at p={p}, k={k}, A={sorted(selected)}')
        witness_satisfies_passes += 2

      with tempfile.TemporaryDirectory(prefix='encodediff-') as directory:
        cnf = Path(directory) / 'case.cnf'
        cnf.write_bytes(direct.dimacs())
        solved = subprocess.run([str(kissat), str(cnf)], check=False, capture_output=True, text=True)
      wanted_sat = bool(expected)
      if solved.returncode not in (10, 20) or (solved.returncode == 10) != wanted_sat:
        raise AssertionError(f'kissat status mismatch at p={p}, k={k}: {solved.returncode}')
      if solved.returncode == 10:
        model = decode_kissat(solved.stdout, p)
        if model not in expected or not verifier_accepts(verifier, p, model):
          raise AssertionError(f'kissat model-decodes failed at p={p}, k={k}, A={sorted(model)}')
        kissat_model_passes += 1

      for name in mutations:
        if mutation_results[name]['detected']:
          continue
        mutant = DirectCnf(p, k, name)
        for selected in (frozenset(values) for values in itertools.combinations(range(p), k)):
          actual = mutant.accepts(selected)
          wanted = selected in expected
          if actual != wanted:
            mutation_results[name] = {
              'detected': True,
              'check': 'oracle truth-table mismatch',
              'p': p,
              'k': k,
              'witness': sorted(selected),
              'direction': 'false SAT / too permissive' if actual else 'false UNSAT / too restrictive',
            }
            break
      records.append({'p': p, 'k': k, 'satisfying': len(expected), 'sha256': digest_sets(expected), 'direct': 'agree', 'cpsat': 'agree', 'each_other': 'agree'})

  if not all(bool(item['detected']) for item in mutation_results.values()):
    output.write_text(json.dumps({'SURVIVING_MUTATIONS': mutation_results}, indent=2) + '\n', encoding='utf-8')
    raise AssertionError('a mutation survived undetected')
  result = {
    'tier': 'TESTED, NOT PROVED',
    'limit': limit,
    'primes': primes,
    'gloss': {'p': 11, 'set': sorted(gloss), 'ordered_counts': ordered_counts(11, gloss), 'usf': oracle_usf(11, gloss)},
    'even_control': {
      'n': 12,
      'set': sorted(even),
      'ordered_counts': ordered_counts(12, even),
      'ordered_criterion': oracle_usf(12, even),
      'campaign_unordered_usf': True,
      'balanced': False,
    },
    'cases': records,
    'mutations': mutation_results,
    'controls': {
      'model_decodes_cpsat_passes': model_decode_passes,
      'model_decodes_kissat_passes': kissat_model_passes,
      'witness_satisfies_encoder_checks': witness_satisfies_passes,
    },
    'elapsed_seconds': round(time.monotonic() - started, 3),
  }
  output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')


def main() -> int:
  parser = argparse.ArgumentParser()
  parser.add_argument('--limit', type=int, required=True)
  parser.add_argument('--kissat', type=Path, required=True)
  parser.add_argument('--verifier', type=Path, required=True)
  parser.add_argument('--output', type=Path, required=True)
  args = parser.parse_args()
  run(args.limit, args.kissat.resolve(), args.verifier.resolve(), args.output.resolve())
  return 0


if __name__ == '__main__':
  raise SystemExit(main())
