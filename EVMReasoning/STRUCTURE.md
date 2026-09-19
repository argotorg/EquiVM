# EVMReasoning/ — structure

Contract- and language-agnostic infrastructure for proving facts about compiled EVM bytecode.
Every per-contract proof is assembled from these files plus contract-specific facts (bytecode
literals, selectors, storage layout) and the coupling lemmas of the spec language it targets
(`Solm/Reasoning/` for Sol⁻, `Solidity/Theory/` for Solidity). Nothing here mentions a spec
language's syntax or semantics.

Everything is in namespace `Reasoning.Theory`, except the EVM trace layer (`RD`, `evm_run`, and the
`RD.*` lemma halves of `Solc.lean`), which is in `Reasoning.Reach`. `JumpDest.lean` has no
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
| `ABI.lean` | Calldata decoding and return-value encoding: per-shape decode lemmas (address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Collapsing chains of memory writes into a canonical form. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `Storage.lean` | Storage maps: red-black-map lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage representation, `accountMapEquiv`/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |

The Sol⁻-coupled halves of the former `Reasoning/` — the coupled loop rule and the `reEquiv*`
builders of `Reach.lean`, the `writeStorage?`/`readStorage?` lemmas of `Storage.lean`, the
`lookupNth?` lemmas of `ABI.lean`, and `SolmBody`, `Dispatch`, `ExternalCall`, `Constructor` —
now live in `Solm/Reasoning/`.

## Dependencies

External: `Ethereum.*` (evmlean — EVM semantics and opcode lemmas), `Storage`, `Refinement`,
`ABI`, Mathlib (EVMWord and Memory only). Transitively still `Solm.Value`, see the root
`STRUCTURE.md`.

Within `EVMReasoning/`, imports flow upward:

```
Stepping   EVMWord
    │         │
    ├── Memory ── MemCascade
    │      │
    │      ├── ABI
    │      └── Reach
    │           │
    └───────── Solc
                │
            Storage

Initcode ← EVMWord     JumpDest ← (Ethereum only)
```

## Where to look

- Run one opcode of a concrete trace → `Stepping` (`<op>_xstep`), chained via `Reach` (`evm_run`).
- Word arithmetic side condition → `EVMWord`.
- Memory read/write or keccak slot → `Memory` (chains of writes: `MemCascade`).
- Decode calldata / encode a return value → `ABI` (solc-specific length checks: `Solc`).
- A code shape the compiler always emits → `Solc`.
- Storage read/write, packed values, bytes/string layout, account-map equivalence → `Storage`.
- Constructor proofs → `Initcode` (and the language's own constructor lemmas).
- Jump-target validity → `JumpDest`.

## Build

`lake build EVMReasoning` builds all ten files; on a small machine build them one at a time
(`Stepping`, `Memory`, `Reach`, `ABI`, `Solc`, `Storage`). A bare `lake build` builds only `Solm`
(the default target) — use explicit targets.
