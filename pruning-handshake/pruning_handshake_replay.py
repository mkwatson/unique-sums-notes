#!/usr/bin/env python3
"""Independent replayer for pruning-handshake schema version 2."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import TextIO


class ReplayError(ValueError):
  def __init__(self, stage: str, message: str) -> None:
    super().__init__(message)
    self.stage = stage


@dataclass(frozen=True)
class Node:
  node_id: str
  state: tuple[int, ...]


def _exact(value: dict[str, object], keys: set[str], label: str, stage: str = 'legitimacy') -> None:
  if set(value) != keys:
    raise ReplayError(stage, f'{label}: fields differ from frozen schema')


def _dict(value: object, label: str) -> dict[str, object]:
  if not isinstance(value, dict):
    raise ReplayError('legitimacy', f'{label}: expected object')
  return value


def _int(value: object, label: str, stage: str = 'legitimacy') -> int:
  if type(value) is not int:
    raise ReplayError(stage, f'{label}: expected integer')
  return value


def _str(value: object, label: str) -> str:
  if not isinstance(value, str) or not value:
    raise ReplayError('legitimacy', f'{label}: expected nonempty string')
  return value


def _state(value: object, modulus: int, k: int, label: str) -> tuple[int, ...]:
  if not isinstance(value, list) or any(type(x) is not int for x in value):
    raise ReplayError('legitimacy', f'{label}: expected integer list')
  state = tuple(value)
  if len(state) != k or tuple(sorted(set(state))) != state or any(x < 0 or x >= modulus for x in state):
    raise ReplayError('legitimacy', f'{label}: invalid k-subset')
  return state


def _fingerprint(state: tuple[int, ...]) -> str:
  payload = json.dumps(list(state), separators=(',', ':')).encode()
  return hashlib.sha256(payload).hexdigest()


def _element(value: object, modulus: int, label: str) -> tuple[int, int]:
  item = _dict(value, label)
  _exact(item, {'multiplier', 'translation'}, label)
  u = _int(item['multiplier'], f'{label}.multiplier')
  t = _int(item['translation'], f'{label}.translation')
  if not (0 <= u < modulus and math.gcd(u, modulus) == 1 and 0 <= t < modulus):
    raise ReplayError('legitimacy', f'{label}: bad permutation outside certified group')
  return u, t


def _image(state: tuple[int, ...], u: int, t: int, modulus: int) -> tuple[int, ...]:
  return tuple(sorted((u * x + t) % modulus for x in state))


def _load(handle: TextIO) -> list[dict[str, object]]:
  result = []
  for line_number, line in enumerate(handle, 1):
    if not line.strip():
      raise ReplayError('legitimacy', f'line {line_number}: blank line')
    try:
      result.append(_dict(json.loads(line), f'line {line_number}'))
    except json.JSONDecodeError as error:
      raise ReplayError('legitimacy', f'line {line_number}: {error.msg}') from error
  return result


def replay(path: Path) -> dict[str, object]:
  with path.open(encoding='utf-8') as handle:
    records = _load(handle)
  if len(records) < 2:
    raise ReplayError('legitimacy', 'stream requires header and end')
  header, end = records[0], records[-1]
  _exact(header, {'record_type', 'format', 'schema_version', 'action', 'root_partition'}, 'header')
  if (header['record_type'], header['format'], header['schema_version']) != ('header', 'pruning-handshake', 2):
    raise ReplayError('legitimacy', 'unsupported header or schema version')
  action = _dict(header['action'], 'action'); _exact(action, {'kind', 'modulus'}, 'action')
  if action['kind'] != 'unit_affine_cyclic': raise ReplayError('legitimacy', 'unsupported action')
  modulus = _int(action['modulus'], 'modulus')
  root = _dict(header['root_partition'], 'root'); _exact(root, {'kind', 'k', 'root_id', 'expected_cell_count'}, 'root')
  k = _int(root['k'], 'k'); expected = _int(root['expected_cell_count'], 'expected_cell_count'); _str(root['root_id'], 'root_id')
  if root['kind'] != 'all_k_subsets' or modulus < 2 or not 0 <= k <= modulus or expected != math.comb(modulus, k):
    raise ReplayError('legitimacy', 'invalid root partition')
  _exact(end, {'record_type', 'partition_node_count', 'retained_count', 'canonical_discard_count', 'group_discard_count', 'infeasibility_count'}, 'end')
  if end['record_type'] != 'end': raise ReplayError('legitimacy', 'last record must be end')

  nodes: dict[str, Node] = {}
  evidence: list[dict[str, object]] = []
  evidence_started = False
  for index, record in enumerate(records[1:-1], 2):
    if record.get('record_type') == 'partition_node':
      if evidence_started: raise ReplayError('legitimacy', f'line {index}: partition node out of order')
      _exact(record, {'record_type', 'node_id', 'path', 'subtree_id', 'state'}, f'line {index}')
      node_id = _str(record['node_id'], 'node_id')
      if node_id in nodes: raise ReplayError('legitimacy', 'duplicate node_id')
      if not isinstance(record['path'], list) or any(not isinstance(x, str) or not x for x in record['path']): raise ReplayError('legitimacy', 'bad path')
      _str(record['subtree_id'], 'subtree_id')
      nodes[node_id] = Node(node_id, _state(record['state'], modulus, k, 'state'))
    else:
      evidence_started = True
      evidence.append(record)

  classified: set[str] = set(); retained: dict[str, tuple[Node, tuple[int, int], tuple[int, ...]]] = {}
  canonical_discards: list[tuple[Node, tuple[int, int], tuple[int, ...], str]] = []
  direct_count = 0; infeasibility_count = 0
  numeric_records: list[tuple[Node, dict[str, object]]] = []
  for index, record in enumerate(evidence):
    kind = record.get('record_type'); label = f'evidence[{index}]'
    if kind == 'canonical_form_witness':
      _exact(record, {'record_type', 'node_id', 'disposition', 'permutation', 'canonical_state', 'fingerprint'}, label)
      node_id = _str(record['node_id'], f'{label}.node_id')
      if node_id not in nodes or node_id in classified: raise ReplayError('legitimacy', f'{label}: missing or duplicate classification')
      disposition = record['disposition']
      if disposition not in ('retained', 'discarded'): raise ReplayError('legitimacy', f'{label}: bad disposition')
      u, t = _element(record['permutation'], modulus, f'{label}.permutation')
      canonical = _state(record['canonical_state'], modulus, k, f'{label}.canonical_state')
      if canonical != _image(nodes[node_id].state, u, t, modulus): raise ReplayError('legitimacy', f'{label}: canonical image mismatch')
      fingerprint = _str(record['fingerprint'], f'{label}.fingerprint')
      if fingerprint != _fingerprint(canonical): raise ReplayError('legitimacy', f'{label}: fingerprint mismatch')
      classified.add(node_id)
      item = (nodes[node_id], (u, t), canonical)
      if disposition == 'retained': retained[node_id] = item
      else: canonical_discards.append((*item, fingerprint))
    elif kind == 'group_element_discard':
      _exact(record, {'record_type', 'source_node_id', 'retained_target_node_id', 'element', 'mapped_state'}, label)
      source_id = _str(record['source_node_id'], 'source_node_id'); target_id = _str(record['retained_target_node_id'], 'retained_target_node_id')
      if source_id not in nodes or source_id in classified or target_id not in nodes: raise ReplayError('legitimacy', f'{label}: bad node identity')
      u, t = _element(record['element'], modulus, f'{label}.element')
      mapped = _state(record['mapped_state'], modulus, k, f'{label}.mapped_state')
      if mapped != _image(nodes[source_id].state, u, t, modulus) or mapped != nodes[target_id].state: raise ReplayError('legitimacy', f'{label}: replayed image mismatch')
      classified.add(source_id); direct_count += 1
    elif kind == 'numeric_infeasibility':
      _exact(record, {'record_type', 'node_id', 'bound_kind', 'arity', 'representation_counts', 'deficits', 'remaining_additions', 'max_repairs_per_addition', 'required_repairs', 'available_repairs'}, label, 'infeasibility')
      node_id = _str(record['node_id'], f'{label}.node_id')
      if node_id not in nodes or node_id in classified: raise ReplayError('legitimacy', f'{label}: missing or duplicate classification')
      classified.add(node_id); infeasibility_count += 1; numeric_records.append((nodes[node_id], record))
    else:
      raise ReplayError('legitimacy', f'{label}: unknown record type')

  # Offline only: construct retained canonical-form index after the complete stream is parsed.
  index: dict[str, list[tuple[Node, tuple[int, int], tuple[int, ...]]]] = {}
  for item in retained.values(): index.setdefault(_fingerprint(item[2]), []).append(item)
  for node, _, canonical, fingerprint in canonical_discards:
    matches = [item for item in index.get(fingerprint, []) if item[2] == canonical]
    if len(matches) != 1: raise ReplayError('completeness', f'offline pairing failed for {node.node_id}: retained canonical-form matches={len(matches)}')
  retained_ids = set(retained)
  for record in evidence:
    if record.get('record_type') == 'group_element_discard' and record['retained_target_node_id'] not in retained_ids:
      raise ReplayError('legitimacy', 'direct target is not classified retained')

  for node, record in numeric_records:
    if record['bound_kind'] != 'singleton_deficit': raise ReplayError('infeasibility', 'unsupported bound kind')
    arity = _int(record['arity'], 'arity', 'infeasibility')
    if arity != modulus: raise ReplayError('infeasibility', 'wrong-arity infeasibility record')
    counts = [0] * modulus
    for a in node.state:
      for b in node.state: counts[(a + b) % modulus] += 1
    deficits = [0 if count == 0 or count >= 3 else 3 - count for count in counts]
    if record['representation_counts'] != counts or record['deficits'] != deficits: raise ReplayError('infeasibility', 'recount or deficit vector mismatch')
    remaining = _int(record['remaining_additions'], 'remaining', 'infeasibility'); cap = _int(record['max_repairs_per_addition'], 'cap', 'infeasibility')
    required = _int(record['required_repairs'], 'required', 'infeasibility'); available = _int(record['available_repairs'], 'available', 'infeasibility')
    if remaining < 0 or cap < 0 or required != sum(deficits) or available != remaining * cap or required <= available:
      raise ReplayError('infeasibility', 'numeric infeasibility inequality not established')

  declared = tuple(_int(end[key], key) for key in ('partition_node_count', 'retained_count', 'canonical_discard_count', 'group_discard_count', 'infeasibility_count'))
  actual = (len(nodes), len(retained), len(canonical_discards), direct_count, infeasibility_count)
  if declared != actual: raise ReplayError('legitimacy', 'end counts mismatch')
  universe = set(combinations(range(modulus), k)); states = [node.state for node in nodes.values()]
  if len(nodes) != expected or len(states) != len(set(states)) or set(states) != universe or classified != set(nodes):
    raise ReplayError('completeness', 'root partition incomplete')
  return {
    'accepted': True, 'schema_version': 2, 'modulus': modulus, 'k': k,
    'legitimacy': {'verdict': 'ACCEPTED', 'canonical_witnesses': len(retained) + len(canonical_discards), 'direct_group_discards': direct_count},
    'completeness': {'verdict': 'ACCEPTED', 'universe_count': len(universe), 'retained_count': len(retained), 'discard_count': len(nodes) - len(retained)},
    'infeasibility': {'verdict': 'ACCEPTED', 'checked_records': infeasibility_count},
  }


def main() -> int:
  parser = argparse.ArgumentParser(); parser.add_argument('stream', type=Path); args = parser.parse_args()
  try: report = replay(args.stream)
  except ReplayError as error:
    stages = ['legitimacy', 'completeness', 'infeasibility']; position = stages.index(error.stage)
    report = {'accepted': False, 'failure_stage': error.stage.upper(), 'error': str(error)}
    for index, stage in enumerate(stages): report[stage] = {'verdict': 'ACCEPTED' if index < position else 'REJECTED' if index == position else 'NOT_EVALUATED'}
    print(json.dumps(report, indent=2, sort_keys=True)); return 1
  print(json.dumps(report, indent=2, sort_keys=True)); return 0


if __name__ == '__main__': raise SystemExit(main())
