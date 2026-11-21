# Safe Benchmark

Source: [`contracts/Safe.sol`](contracts/Safe.sol) from `safe-global/safe-smart-account` commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57` (2026-06-05, `Do Not Propagate Reverts on Signatures (#1115)`).

Compiled with Solidity 0.8.35 through the IR pipeline and optimizer enabled, from the repository root:

```bash
solc --via-ir --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none --bin --bin-runtime --abi --storage-layout \
  --base-path . --overwrite -o /tmp/safe-viair-build Benchmarks/Safe/ViaIR/contracts/Safe.sol
```

Compiler: `0.8.35+commit.47b9dedd.Linux.g++`. Only `--via-ir` differs from the
legacy compiler settings. The audit reproduces both bytecode files and the ABI exactly.

The EVM target is pinned to Shanghai to reproduce the original artifacts. The current local
EVM semantics also implement `MCOPY`; changing the compiler target would still change the
benchmark bytecode and is not part of this audit.

Some vendored upstream Solidity comments still mention the historical 0.7.6 compiler or link to
0.7.6 documentation; those comments are not the benchmark compiler pin.  The command above is the
artifact provenance for this benchmark.

Artifacts:

- `creation.hex`: optimized creation bytecode, 11034 bytes, sha256 `60f584185471210453fd3e9aa6f4f994daf1eec6465f5b5cd3ed3457d966fa26`
- `runtime.hex`: optimized deployed runtime bytecode, 11003 bytes, sha256 `01ed7613d9170c16d92505d5db5eb71ad2179f9b0435a3bb077b7f4b71833f97`
- `Safe.abi.json`: ABI emitted by solc, sha256 `40069244550920fc4ecdb4a162f9b45c78b5de06fc7fdcb8f7d4350739bb8682`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Stele AST with ABI surface, solc 0.8.35 decoding, and physical storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: proved constructor equivalence for the IR bytecode
- `Correct.lean`: proved runtime and whole-contract refinement for the IR bytecode
- `CorrectProofAudit.lean`: checks the constructor, runtime, and whole-contract axiom footprints
- `Runtime.lean`: 33 entrypoint obligations (31 selectors, receive, fallback)
- `Blocks.lean`, `Blocks/`: generated runtime and constructor instruction summaries and PC indexes
- `ArtifactChecks.lean`: executable checks of every ABI signature, selector, and return type
- `Audit.lean`, `AuditSupport.lean`: differential regressions against the actual EVM interpreter
- `AuditManifest.json`: reproducible compiler, ABI, storage, instruction, event, and boundary inventory

Main source sha256: `9f91d9250e18bb0710b7b1f10dcbe2417e9ef8d22eeee98dba2ef48661a060fa`.

## Refinement scope and specification corrections

The constructor, all 33 runtime entrypoints, and the whole-contract refinement are proved.
The runtime and whole-contract claims require the executing account to exist:
`σ.get? I.codeOwner ≠ none`. This approved premise is needed by owner insertion because the
model permits code execution independently of account existence, while storage writes to an
absent account are no-ops. The constructor and the other 32 entrypoint statements retain their
original premises. No additional gas bound is imposed.

The port exposed differences between the generated IR checks and the copied specification on
symbolic inputs. The user approved these benchmark-local corrections:

| Surface | Correction |
| --- | --- |
| Zero-argument decoding | Reject `calldata.size - 4 >= 2^255` for empty parameter lists. Other parameter lists use the existing `modern` decoder. |
| `getStorageAt` | Bound the wrapped requested byte length by `2^64 - 161`, accounting for the allocation header and initial free pointer. |
| `getOwners` | Bound the owner count by `2^59 - 6`. |
| `getModulesPaginated` | Bound the requested page size by `2^59 - 6`. |
| `setup` | After `SafeSetup`, require `32 * owners.length + data.length <= 2^64 - 352` for positive token payments, and `<= 2^64 - 224` otherwise. |

The setup guard accounts for the owner and data buffers and, where needed, the token encoder's
additional 128 bytes. It preserves the event's position before the allocation and owner checks.
The shared decoding modes and vendored Solidity sources are unchanged. The AST and syntax
specifications agree definitionally. See [`REPAIR.md`](REPAIR.md) for the proof and validation
summary.

The refinement relation observes final account maps, successful return bytes, reverts,
invalid-instruction halts, and static-mode violations. Gas exhaustion has a separate refinement
case. Log contents and revert payloads are not observed; external-call gas and input substates
are existential witnesses. For example, the native-payment allocation-failure proof uses a
proved failing zero-gas call when the actual call returns nonempty data. These are properties
of the repository's refinement model, rather than equality of all production-EVM observables.

The executable audit covers all selectors, permission and call-value checks, malformed ABI
heads, dirty storage, linked lists, calldata aliases, guards, signatures, token return values,
refunds, delegatecall storage changes, depth limits, and construction. It compares successful
return bytes and the entire final account map. Call replay checks opcode, target, value,
calldata, and the account map before each call. This audit is independent of the proofs.

The regression audit passes 408 cases: 104 successes, 292 reverts, 11 static violations, and
one separately classified out-of-gas result. The final randomized run reports:

```text
Safe_ViaIR: 1775 cases: 1762 agree (580 successful), 0 disagree, 0 stuck, 13 EVM out of gas, 0 spec out of fuel
```

## Generated summaries and proof obligations

There are 1,871 runtime summary theorems in 49 shards, plus seven constructor summary theorems.
These are generated using the existing RD opcode lemmas. Both sides of every conditional jump
are indexed. Runtime summaries cover 6,974 instructions; the remaining 26 instruction sites are
explicit boundaries, not assumed transitions:

- `CALL`: 92, 4881, 5080, 5214, 5338, 5650, 9989, 10188, 10344, 10513, 10627.
- `STATICCALL`: 1637, 1928, 7776, 8460, 8678.
- `DELEGATECALL`: 3524, 3987, 4708, 10175.
- `ORIGIN`: 5002, 10450.
- `GASPRICE`: 5047, 5112, 10482.
- `EXTCODECOPY`: 10963.

Every analyzed instruction is accounted for by a summary or a recorded boundary. Constructor
summaries cover only PCs 0–30; the runtime at offset 31 is copied data. They quantify an arbitrary
constructor-argument tail against the full creation bytecode. Solidity CBOR metadata is excluded
from runtime instruction analysis. Summary hypotheses such as valid jump destinations, stack
bounds, and static permission are discharged in the entrypoint proofs. Shared routine proofs
compose the summaries, with separate proofs for internal callees and source-level call wrappers.

## Reproduction and validation

From the repository root, using the pinned compiler:

```bash
python3 -B scripts/audit_safe.py --dir Benchmarks/Safe/ViaIR --via-ir --solc /path/to/solc-0.8.35
lake build Benchmarks.Safe.ViaIR.ArtifactChecks Benchmarks.Safe.ViaIR.SpecSyntax
lake build Benchmarks.Safe.ViaIR.Correct Benchmarks.Safe.ViaIR.Audit
lake build Benchmarks.Safe.ViaIR.CorrectProofAudit Benchmarks.Safe.ViaIR.GetOwnersModelAudit
lake env lean Benchmarks/Safe/ViaIR/Audit.lean
lake exe stele-difftest --only Safe_ViaIR --count 50
```

The Python check recompiles source, verifies every source hash and both Lean byte arrays, checks
the ABI/dispatcher agreement, and checks that generated files match their current generator.
Add `--write` to regenerate summaries, indexes, ABI checks, and the manifest. It does not fill
refinement proofs. The SHA-256 values in the artifact list above hash the **hex text files**;
the manifest separately records hashes of the decoded bytecode bytes.
