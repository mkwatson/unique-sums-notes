#!/usr/bin/env python3
"""Convert preserved SELFPRUNE artifacts to pruning-handshake schema v2."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import TextIO


def _write(handle: TextIO, value: dict[str, object]) -> None:
  handle.write(json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n')


def _canonical(state: tuple[int, ...], modulus: int) -> tuple[tuple[int, ...], int, int]:
  candidates = []
  for u in range(modulus):
    if math.gcd(u, modulus) != 1: continue
    for t in range(modulus): candidates.append((tuple(sorted((u * x + t) % modulus for x in state)), u, t))
  return min(candidates)


def _fingerprint(state: tuple[int, ...]) -> str:
  return hashlib.sha256(json.dumps(list(state), separators=(',', ':')).encode()).hexdigest()


def _numeric(state: tuple[int, ...], modulus: int, node_id: str) -> dict[str, object]:
  counts = [0] * modulus
  for a in state:
    for b in state: counts[(a + b) % modulus] += 1
  deficits = [0 if count == 0 or count >= 3 else 3 - count for count in counts]
  if not sum(deficits): raise ValueError('state has no singleton deficit')
  return {
    'record_type': 'numeric_infeasibility', 'node_id': node_id, 'bound_kind': 'singleton_deficit',
    'arity': modulus, 'representation_counts': counts, 'deficits': deficits,
    'remaining_additions': 0, 'max_repairs_per_addition': 0,
    'required_repairs': sum(deficits), 'available_repairs': 0,
  }


def convert(source: Path, destination: Path, numeric_leaf_prunes: bool = False) -> dict[str, int]:
  raw = json.loads(source.read_text(encoding='utf-8'))
  if not isinstance(raw, dict) or raw.get('format') != 'selfprune-affine-v1': raise ValueError('unsupported SELFPRUNE artifact')
  p, k, retained_raw, prunes_raw = raw.get('p'), raw.get('k'), raw.get('retained'), raw.get('prunes')
  if type(p) is not int or type(k) is not int or not isinstance(retained_raw, list) or not isinstance(prunes_raw, list): raise ValueError('malformed artifact')
  retained_states = {tuple(entry['object']) for entry in retained_raw}
  discarded_states = {tuple(entry['discarded']) for entry in prunes_raw}
  states = sorted(retained_states | discarded_states)
  ids = {state: f'leaf-{index:04d}' for index, state in enumerate(states)}
  canonical_discards = 0; numeric_count = 0
  with destination.open('w', encoding='utf-8') as handle:
    _write(handle, {'record_type': 'header', 'format': 'pruning-handshake', 'schema_version': 2, 'action': {'kind': 'unit_affine_cyclic', 'modulus': p}, 'root_partition': {'kind': 'all_k_subsets', 'k': k, 'root_id': f'C({p},{k})', 'expected_cell_count': math.comb(p, k)}})
    for state in states: _write(handle, {'record_type': 'partition_node', 'node_id': ids[state], 'path': [f'lexicographic-rank:{ids[state][5:]}'], 'subtree_id': 'SELFPRUNE-leaf-partition', 'state': state})
    for state in states:
      if state in discarded_states and numeric_leaf_prunes:
        _write(handle, _numeric(state, p, ids[state])); numeric_count += 1; continue
      canonical, u, t = _canonical(state, p)
      disposition = 'retained' if state in retained_states else 'discarded'
      _write(handle, {'record_type': 'canonical_form_witness', 'node_id': ids[state], 'disposition': disposition, 'permutation': {'multiplier': u, 'translation': t}, 'canonical_state': canonical, 'fingerprint': _fingerprint(canonical)})
      if disposition == 'discarded': canonical_discards += 1
    _write(handle, {'record_type': 'end', 'partition_node_count': len(states), 'retained_count': len(retained_states), 'canonical_discard_count': canonical_discards, 'group_discard_count': 0, 'infeasibility_count': numeric_count})
  return {'partition_node_count': len(states), 'retained_count': len(retained_states), 'canonical_discard_count': canonical_discards, 'infeasibility_count': numeric_count}


def main() -> int:
  parser = argparse.ArgumentParser(); parser.add_argument('source', type=Path); parser.add_argument('destination', type=Path); parser.add_argument('--numeric-leaf-prunes', action='store_true'); args = parser.parse_args()
  print(json.dumps(convert(args.source, args.destination, args.numeric_leaf_prunes), indent=2, sort_keys=True)); return 0


if __name__ == '__main__': raise SystemExit(main())
