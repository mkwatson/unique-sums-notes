#!/usr/bin/env python3
"""Materialize and count one negative control for each v2 verdict path."""

from __future__ import annotations

import json
import tempfile
from pathlib import Path

from convert_selfprune_handshake import convert
from pruning_handshake_replay import ReplayError, replay


HERE = Path(__file__).resolve().parent


def read(path: Path) -> list[dict[str, object]]:
  return [json.loads(line) for line in path.read_text(encoding='utf-8').splitlines()]


def write(path: Path, records: list[dict[str, object]]) -> None:
  path.write_text(''.join(json.dumps(record, sort_keys=True) + '\n' for record in records), encoding='utf-8')


def main() -> int:
  results: list[dict[str, object]] = []
  with tempfile.TemporaryDirectory() as directory:
    root = Path(directory); canonical = root / 'canonical.jsonl'; numeric = root / 'numeric.jsonl'
    convert(HERE / 'SELFPRUNE-p11-k7.json', canonical)
    convert(HERE / 'SELFPRUNE-p11-k5.json', numeric, numeric_leaf_prunes=True)
    for name, baseline in (('bad-permutation', canonical), ('wrong-arity-infeasibility', numeric), ('deleted-orbit', canonical)):
      records = read(baseline)
      if name == 'bad-permutation':
        witness = next(x for x in records if x['record_type'] == 'canonical_form_witness')
        witness['permutation'] = {'multiplier': 0, 'translation': 0}
      elif name == 'wrong-arity-infeasibility':
        record = next(x for x in records if x['record_type'] == 'numeric_infeasibility'); record['arity'] = 10
      else:
        retained = next(x for x in records if x.get('record_type') == 'canonical_form_witness' and x.get('disposition') == 'retained')
        fingerprint = retained['fingerprint']
        deleted = {x['node_id'] for x in records if x.get('record_type') == 'canonical_form_witness' and x.get('fingerprint') == fingerprint}
        records = [x for x in records if not ((x.get('record_type') == 'partition_node' and x.get('node_id') in deleted) or (x.get('record_type') == 'canonical_form_witness' and x.get('node_id') in deleted))]
        records[-1]['partition_node_count'] -= len(deleted); records[-1]['retained_count'] -= 1; records[-1]['canonical_discard_count'] -= len(deleted) - 1
      path = root / f'{name}.jsonl'; write(path, records)
      try: replay(path)
      except ReplayError as error: results.append({'name': name, 'firing_count': 1, 'failure_stage': error.stage.upper(), 'reason': str(error)})
      else: results.append({'name': name, 'firing_count': 0, 'failure_stage': 'NONE', 'reason': 'accepted'})
  report = {'control_count': 3, 'total_firing_count': sum(int(x['firing_count']) for x in results), 'results': results}
  (HERE / 'HANDSHAKE-negative-controls-v2.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
  print(json.dumps(report, indent=2, sort_keys=True))
  actual = [(x['failure_stage'], x['firing_count']) for x in results]
  return 0 if actual == [('LEGITIMACY', 1), ('INFEASIBILITY', 1), ('COMPLETENESS', 1)] else 1


if __name__ == '__main__': raise SystemExit(main())
