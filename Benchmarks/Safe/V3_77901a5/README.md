# Safe Benchmark

Source: [`contracts/Safe.sol`](contracts/Safe.sol) from `safe-fndn/safe-smart-account` commit `77901a5a1ad835b74ad3b72f73a8412cfe491c57`.

Compiled with Solidity 0.8.35 and optimizer enabled, from the repository root:

```bash
solc --optimize --optimize-runs 200 --evm-version shanghai --metadata-hash none --bin --bin-runtime --abi --storage-layout \
  --base-path . --overwrite -o /tmp/safe-v3-build Benchmarks/Safe/V3_77901a5/contracts/Safe.sol
```

Pinned compiler: `0.8.35+commit.47b9dedd.Linux.g++`, sha256
`fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4`.

The EVM target is pinned to Shanghai to reproduce the original artifacts. The current local
EVM semantics also implement `MCOPY`; changing the compiler target would still change the
benchmark bytecode and is not part of this audit.

Some vendored upstream Solidity comments still mention the historical 0.7.6 compiler or link to
0.7.6 documentation; those comments are not the benchmark compiler pin.  The command above is the
artifact provenance for this benchmark.

Artifacts:

- `creation.hex`: optimized creation bytecode, 11907 bytes, sha256 `4ec4d14f59ce96302ff8b416bd7beaa5e7d1578b4e50f48fb9ac51d1a5fbe78c`
- `runtime.hex`: optimized deployed runtime bytecode, 11874 bytes, sha256 `406b84a059e1ba6ec27fbe630072710c3e13745ed9343e3b128a32cbcd4de4b6`
- `Safe.abi.json`: ABI emitted by solc, sha256 `40069244550920fc4ecdb4a162f9b45c78b5de06fc7fdcb8f7d4350739bb8682`
- `sources.sha256`: sha256 manifest for the vendored Solidity source tree
- `Spec.lean`: Stele AST with ABI surface, solc 0.8.35 decoding, and physical storage layout
- `SpecSyntax.lean`: syntax-side wrapper checked definitionally against the AST scaffold
- `Bytecode.lean`: optimized bytecode embedded as `ByteArray`, with `valid_jumps` facts
- `Constructor.lean`: proved constructor equivalence
- `Correct.lean`: proved runtime and whole-contract refinement
- `CorrectProofAudit.lean`: checks the constructor, runtime, and whole-contract axiom footprints
- `Runtime.lean`: 33 proved entrypoint obligations (31 selectors, receive, fallback)
- `Blocks.lean`, `Blocks/`: generated runtime and constructor instruction summaries and PC indexes
- `ArtifactChecks.lean`: executable checks of every ABI signature, selector, and return type
- `Audit.lean`, `AuditSupport.lean`: differential regressions against the actual EVM interpreter
- `AuditManifest.json`: reproducible compiler, ABI, storage, instruction, event, and boundary inventory

Main source sha256: `9f91d9250e18bb0710b7b1f10dcbe2417e9ef8d22eeee98dba2ef48661a060fa`.

## Semantic audit

The audit target is the pinned bytecode under the repository's current `Stele.runtimeRefinement`.
That relation observes the final account map, successful return bytes, reverts, invalid-instruction
halts, and static-mode violations. Gas exhaustion has its own refinement case. Gas observations
and call gas/substate inputs are existential witnesses. Log contents and revert payloads are not
observed. Consequently this is not a claim of equivalence for all observables of a production EVM.

The constructor and all runtime obligations are proved. The proofs handle gas exhaustion through
the refinement relation's out-of-gas cases and use the actual EVM call result for external calls.
No additional well-formed-storage, successful-decoding, nonstatic, or restricted-callee assumptions
were needed. The trusted base consists of Lean's standard axioms and concrete `native_decide`
evaluation facts; selector identities use kernel evaluation.

Corrections made during the audit:

| Area | Bytecode evidence and specification behavior |
| --- | --- |
| Events and static mode | All 17 `LOG` sites now have event statements in source order. Receive emits at PC 533. Setup emits at PC 4634 **before** its threshold/owner checks. Module events follow the post-guard; transaction events precede the post-guard. |
| Assembly address stores | PCs 5944, 6194, and 8317 perform whole-word `SSTORE` for module guard, guard, and fallback handler. Their locators now have size 32; ordinary address mappings retain 20-byte writes preserving unrelated high bits. |
| Fallback raw-word check | PCs 581–586 test the entire handler slot. A nonzero word with zero low 160 bits still calls address zero. The spec reads the raw word before converting the call target to an address. |
| Allocation panics | The explicit `new` size guards for owners, module pages, and raw storage bytes are retained. `getStorageAt` checks the wrapped `length << 5`, not unbounded multiplication. |
| Memory argument decoding | The decoder at PC 9242 checks its new free-memory pointer. Its sole memory `bytes` argument starts at 0x80, so `0x80 + 32 + ceil32(length) <= 2^64 - 1` requires `length <= 2^64 - 192`. All eight affected entrypoints now check this; calldata-only arguments do not. |
| Signature dispatch | `v = 2` selects the P-256 branch at PC 2209. It checks the dynamic offset and 128-byte payload, derives the signer from the public-key hash, then calls `p256Verify`. Other values besides 0, 1, 2, or greater than 30 use ordinary ecrecover. |
| P-256 verification | `STATICCALL` at PC 7150 sends five words to address `0x100`. PCs 7151–7161 accept only call success with exactly 32 return bytes containing the word 1; empty, short, oversized, non-one, or failed returns are rejected. |
| Contract signatures | The low-level `STATICCALL` at PC 8796 returns a success flag. PCs 8852–8871 require success and exactly 32 return bytes; the decoder at PC 11787 loads the whole word, and PC 8903 compares it with the padded ERC-1271 magic value. Failed calls, noncanonical words, and trailing data produce `false`; the caller at PC 7053 then reverts with `GS024`. |
| Self owners | Setup, add, remove, and swap reject zero/sentinel owner addresses. A self owner is accepted only when `EXTCODECOPY` at PC 9062 reads the zero-padded prefix `ef0100`; the shared guard at PC 8589 enforces this for both added and removed owners. |
| Execution order | Nonce increment precedes transaction hashing, as in the `nonce++` argument evaluation. Raw storage slot addition is explicitly reduced to 256 bits. |

The remaining behavior was checked against the vendored sources, the exactly reproduced compiler
output, its generated ABI decoder code, and source-mapped instructions:

| Surface | Checks retained |
| --- | --- |
| Dispatcher, receive, fallback | All 31 selectors, short and unknown selectors, per-entrypoint payability, decoding failures, empty calldata, caller suffix, raw success return, and propagated call failure. |
| Owner management | Authorization, sentinel and zero restrictions, conditional self-address restriction on every owner change, duplicate owners, linked-list rewiring, checked count changes, threshold updates, malformed lists and array bounds. |
| Module management | Enable/disable authorization, sentinel membership, page allocation and truncation, last-element continuation, broken zero links, cached guard, call/delegatecall distinction, return-data capture before post-guard. |
| Setup and constructor | Constructor writes only threshold after its value check. Setup event order, single initialization, owner setup, full-word fallback store, code-existence check for setup delegatecall, and optional payment. |
| Signatures | Both compatibility overloads, ignored data preimages, checked `requiredSignatures * 65`, ordered owners, all `v` branches, dynamic bounds and overflow checks, approved hashes, exact-word ERC-1271 validation and failed-call rejection, P-256 dynamic bounds and signer derivation, exact P-256 return decoding, ecrecover failure. |
| Transaction and payment | EIP-712 constants/encoding, nonce timing, enum validation, guard checks, checked additions and wrapping shift in gas check, failure policy, native refund price cap/origin, ERC-20 empty/32-byte/nonzero acceptance, and event/post-guard ordering. |
| Views and simulation | Scalar and mapping getters, flattened tuple returns, domain/transaction hashes, modulo raw storage addressing, delegatecall effects followed by unconditional revert. |
| Calls | Correct caller/value/permission inheritance, depth and balance failures, arbitrary target code, raw return data, typed bool validation, missing code on void calls, and callee world effects. |

`Audit.lean` runs every selector in both permission modes and with zero/nonzero call value, then
checks malformed ABI heads, dirty storage, linked lists, calldata aliases, guard return sizes,
contract signatures, P-256 inputs and return conventions, self owners, token return conventions, refunds, delegatecall storage changes,
depth limits, and construction. It compares success return bytes and the entire final account map.
Call replay also checks opcode, target, value, calldata, and the account map before every call.
The owner validity expression includes the short-circuit EIP-7702 probe. The compiled shared
owner helpers implement the same checks before linked-list writes. Contract-signature validation uses a helper for the
low-level static call and exact-word magic-value comparison.
The harness reports out-of-gas separately and fails on test-fuel exhaustion or unsupported AST
forms. It is independent of the refinement proofs.

The recorded regression run passed all 468 cases: 116 successes, 340 reverts, 11 static-mode
violations, and one separately classified out-of-gas result. The targeted Lake build includes
the specification equality check, ABI checks, refinement proofs, and all generated summaries.

## Generated summaries and proof obligations

There are 1,937 runtime summary theorems in 51 shards, plus seven constructor summary theorems.
These are generated using the existing RD opcode lemmas. Both sides of every conditional jump
are indexed. Runtime summaries cover 7,844 instructions; the remaining 20 instruction sites are
explicit boundaries, not assumed transitions:

- `CALL`: 614, 3738, 4235, 7345, 7464, 7565, 7834, 9004.
- `STATICCALL`: 2554, 2651, 5833, 6083, 7150, 8796.
- `DELEGATECALL`: 4535, 7445.
- `ORIGIN`: 7754.
- `GASPRICE`: 7775, 7782.
- `EXTCODECOPY`: 9062.

Every analyzed instruction is accounted for by a summary or a recorded boundary. Constructor
summaries cover only PCs 0–32; the runtime at offset 33 is copied data. They quantify an arbitrary
constructor-argument tail against the full creation bytecode. Solidity CBOR metadata is excluded
from runtime instruction analysis. Summary hypotheses such as valid jump destinations, stack
bounds, and static permission are discharged in the entrypoint proofs. Shared routine proofs
compose the summaries, with separate proofs for internal callees and source-level call wrappers.

## Reproduction and validation

From the repository root, using the pinned compiler:

```bash
python3 -B scripts/audit_safe.py --dir Benchmarks/Safe/V3_77901a5 --solc /path/to/solc-0.8.35
lake build Benchmarks.Safe.V3_77901a5.ArtifactChecks Benchmarks.Safe.V3_77901a5.SpecSyntax
lake build Benchmarks.Safe.V3_77901a5.Correct Benchmarks.Safe.V3_77901a5.Audit
lake build Benchmarks.Safe.V3_77901a5.CorrectProofAudit Benchmarks.Safe.V3_77901a5.GetOwnersModelAudit
lake env lean Benchmarks/Safe/V3_77901a5/Audit.lean
```

The Python check recompiles source, verifies every source hash and both Lean byte arrays, checks
the ABI/dispatcher agreement, and checks that generated files match their current generator.
Add `--write` to regenerate summaries, indexes, ABI checks, and the manifest. It does not fill
refinement proofs. The SHA-256 values in the artifact list above hash the **hex text files**;
the manifest separately records hashes of the decoded bytecode bytes.

The randomized differential test reports:

```text
Safe_V3_77901a5: 1775 cases: 1761 agree (578 successful), 0 disagree, 0 stuck, 14 EVM out of gas, 0 spec out of fuel
```

The EVM dependency implements cryptography in Lean. Run the randomized suite from the
repository root; no Python cryptography environment is needed:

```bash
lake exe stele-difftest --only Safe_V3_77901a5 --count 50
```
