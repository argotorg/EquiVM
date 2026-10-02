# EVMReasoning/ — structure

Contract- and language-agnostic infrastructure for proving facts about compiled EVM bytecode.
Every per-contract proof is assembled from these files plus contract-specific facts (bytecode
literals, selectors, storage layout) and the coupling lemmas of the spec language it targets
(`Solm/Reasoning/` for Sol⁻, `Solidity/Theory/` for Solidity). Nothing here mentions a spec
language's syntax or semantics.

Everything is in namespace `Reasoning.Theory`, except the EVM trace layer (`RD`, `evm_run`, and the
`RD.*` lemma halves of `Solc.lean`), which is in `Reasoning.Reach`, and its successor `Trace.lean` (`Run`, `Returned`, `Reverted`) together with
`SolcTrace.lean` and `SolcIdioms.lean`, which are in `Reasoning.Trace`. `JumpDest.lean` has no
namespace (it defines a tactic and an attribute).

One axiom in the whole library: `keccak_size` in `Memory.lean` (a keccak digest is 32 bytes —
trusted spec of the FFI hash; asserts nothing about collision resistance).

## Files

| File | Contents |
|---|---|
| `Stepping.lean` | Base layer. Trace drivers — `initState` (the fresh EVM state), the `Ξ`-to-iterator bridge (`Xi_*_of_X`), single-step peeling (`X_peel`, `stepContinue`, `stepOOG`, `stepHalt*`) — plus one lemma per opcode (`<op>_xstep`) evaluating a single `Xstep` to an explicit gas-guarded successor state (`st<Op>` definitions). |
| `EVMWord.lean` | `UInt256` arithmetic: no-wrap `toNat` lemmas, bitwise normalization, unsigned comparisons, signed `SLT`, `compare` order instances, the word-rounding used by solc memory allocation. |
| `Memory.lean` | Byte-level memory: little-endian word arithmetic, `MSTORE`/`MLOAD` read-write facts, scratch memory for mapping hashes, selector extraction, calldata decode coupling, mapping-slot keccak facts. Home of the `keccak_size` axiom. |
| `Reach.lean` | The EVM trace layer. `RD` (reached-or-out-of-gas invariant), one forward step lemma per opcode (`RD.<op>`), `CALL`/`STATICCALL` with the callee treated as an opaque `Θ` result, terminal forms `RDret`/`RDrev` with `xiResult`, `Cursor`/`RDc`, and the `evm_run` macro that chains steps with auto-discharged decode/overflow side conditions. |
| `Trace.lean` | The successor of `Reach.lean`: `Run` (reached-or-out-of-gas over a `Cursor` — machine state plus a `World` of accounts and event log — from the initial state; no duplicated run constants), one step lemma per opcode via the generic `Run.step`/`Run.stepVar` (memory instructions also in a `*Var` form with the expansion cost read from the state, for symbolic offsets), `CALL` with the callee's substate exposed, selector dispatch, the cursor-valued while-rule and its counting-loop instance, and the terminals `Returned` (world and output) / `Reverted` (exact revert data) with their `Ξ` bridges. Reuses Reach's `evm_run`/`evm_ov`/`mem_cost` and bytecode-shape definitions; namespace `Reasoning.Trace`. |
| `ABI.lean` | Calldata decoding and return-value encoding on `ABIValue`: per-shape positional decode lemmas (`decodeCalldataValues_*`: address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Collapsing chains of memory writes into a canonical form. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `SolcTrace.lean` | The trace-level lemmas of `Solc.lean` restated on `Run`/`Returned`/`Reverted` (same names under `Run.`): every revert states its exact data (`ByteArray.empty` stubs, the `Error(string)` payload `solcErrorStringPayload`, the bubbled return data of a failed call), the `LOG3` suffixes expose the appended `LogEntry`, `STATICCALL` exposes the callee substate. Reuses all pure facts of `Solc.lean`; adds `*Wf` bundles for the external-argument decoders. |
| `SolcIdioms.lean` | Compiler shapes that were only proved inside individual example proofs, generalised on `Run`: `Panic(uint256)` tails (inline and shared-routine forms) with the exact payload `solcPanicPayload`, the optimized checked addition with `Panic(0x11)`, dynamic storage arrays (data-area slot, index bounds guard, `for` header over the array length, counter increment), the shared return block with its word/address encoders, the byte-array length decoder (`Panic(0x22)` on a malformed header), and the custom-error tails (selector store at `0x80`, revert blocks, `Run.solcCustomErrorRevert`, `Run.solcErrorArgWordInline`/`Run.solcCustomErrorRevertU256` (`revert E(x)`, inline one-word encoder) for `revert E()`). |
| `Storage.lean` | Storage maps: red-black-map lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage representation, `accountMapEquiv`/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |

The Sol⁻-coupled halves of the former `Reasoning/` — the coupled loop rule and the `reEquiv*`
builders of `Reach.lean`, the `writeStorage?`/`readStorage?` lemmas of `Storage.lean`, the
`lookupNth?` lemmas of `ABI.lean`, and `SolmBody`, `Dispatch`, `ExternalCall`, `Constructor` —
now live in `Solm/Reasoning/`.

## Dependencies

External: `Ethereum.*` (evmlean — EVM semantics and opcode lemmas), `Storage`, `Refinement`,
`ABI`, Mathlib (EVMWord and Memory only). `Storage.lean` also imports `Solm.Value` for the
mapping-key words (`keyValueToWord`), see the root `STRUCTURE.md`.

Within `EVMReasoning/`, imports flow upward:

```
Stepping   EVMWord
    │         │
    ├── Memory ── MemCascade
    │      │
    │      ├── ABI
    │      └── Reach ── Trace ── SolcTrace ── SolcIdioms
    │           │                   │
    └───────── Solc ────────────────┘
                │
            Storage

Initcode ← EVMWord     JumpDest ← (Ethereum only)
```

## Where to look

- Run one opcode of a concrete trace → `Stepping` (`<op>_xstep`), chained via `Reach` (`evm_run`).
- Word arithmetic side condition → `EVMWord`.
- Memory read/write or keccak slot → `Memory` (chains of writes: `MemCascade`).
- Decode calldata / encode a return value → `ABI` (solc-specific length checks: `Solc`).
- A code shape the compiler always emits → `Solc` (on `Run`: `SolcTrace`; Panic tails, arrays, loops, return block, byte-array length: `SolcIdioms`).
- Storage read/write, packed values, bytes/string layout, account-map equivalence → `Storage`.
- Constructor proofs → `Initcode` (and the language's own constructor lemmas).
- Jump-target validity → `JumpDest`.

## Build

`lake build EVMReasoning` builds all thirteen files; on a small machine build them one at a time
(`Stepping`, `Memory`, `Reach`, `ABI`, `Solc`, `Storage`). A bare `lake build` builds only `Solm`
(the default target) — use explicit targets. `Storage.lean` also gained `int256Loc`, `s256OfWord`, `storageLocLoad_full_word` (any full-slot element type decodes the word), `storageLocLoad_int256`/`storageLocStore_int256` (two's-complement word ↔ `Int`), `s256OfWord_wordOfInt`, `s256OfWord_bounds`. Packed fields: `storageLocLoad_offset_word` (any element type), `storageLocLoad_sint_offset`/`sextAt` (sign-extended packed signed read), `storageLocStore_int_packed` (packed store of any `.int` value).
