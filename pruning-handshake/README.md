# Pruning handshake v2

Schema v2 has two primary evidence records. `canonical_form_witness` records the
canonical-labelling permutation and fingerprint already computed for each retained or
discarded node. The replayer builds the retained fingerprint index after the run and pairs
discards offline. `numeric_infeasibility` separately certifies singleton-deficit pruning.
Engines that already compute explicit discard-to-retained mappings may instead use the
`group_element_discard` profile.

The canonical-form profile matches canonical-augmentation engines. Its cheapest logging
addition is to preserve the canonical-labelling permutation and canonical-form fingerprint
already used by the accept/reject test, plus a prune-reason tag. Do not add a live retained-node
index. McKay's finding is that canonical augmentation exposes the node-to-canonical permutation
but does not naturally identify a retained collision partner during DFS.

Run `python3 pruning_handshake_replay.py HANDSHAKE-p11-k7-v2.jsonl`. Run
`python3 handshake_negative_controls.py` for the bad-permutation, wrong-arity-infeasibility,
and deleted-orbit controls.

For the included canonical sample, the result is **CHECKER-VERIFIED EXHAUSTIVE FINITE
COVERAGE** at $(11,7)$. The infeasibility fixture is an exact leaf check at $(11,5)$.
The package does not certify an engine's internal traversal, encoder, serialization, or solver
verdict. For non-leaf numeric pruning, the engine-specific repair-capacity bound remains an
explicit trust boundary unless separately certified.
