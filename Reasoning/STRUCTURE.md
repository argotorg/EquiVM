# Reasoning/ — structure

Shared, contract-agnostic infrastructure for proving that compiled EVM bytecode refines its Solm
specification. Every per-contract proof in `Examples/` and `Benchmarks/` is assembled from these
files plus contract-specific facts (bytecode literals, selectors, storage layout).

Everything is in namespace `Reasoning.Theory`, except the EVM trace layer (`RD`, `evm_run`, and the
`RD.*` lemma halves of `Solc.lean` and `Dispatch.lean`), which is in `Reasoning.Reach`.
`JumpDest.lean` has no namespace (it defines a tactic and an attribute).

One axiom in the whole library: `keccak_size` in `Memory.lean` (a keccak digest is 32 bytes —
trusted spec of the FFI hash; asserts nothing about collision resistance).

## Files

| File | Contents |
|---|---|
| `Stepping.lean` | Base layer. Trace drivers — `initState` (the fresh EVM state), the `Ξ`-to-iterator bridge (`Xi_*_of_X`), single-step peeling (`X_peel`, `stepContinue`, `stepOOG`, `stepHalt*`) — plus one lemma per opcode (`<op>_xstep`) evaluating a single `Xstep` to an explicit gas-guarded successor state (`st<Op>` definitions). |
| `EVMWord.lean` | `UInt256` arithmetic: no-wrap `toNat` lemmas, bitwise normalization, unsigned comparisons, signed `SLT`, `compare` order instances, the word-rounding used by solc memory allocation. |
| `SolmBody.lean` | The Solm side: `ExecTransitionBody`/`ExecStmt`/`ExecBlock` lemmas. Non-payable guard, call wrappers (external/checked/low-level/delegate), loop rules, block sequencing (`execBlock_append`), locals lookup, storage-access collapse. |
| `Memory.lean` | Byte-level memory: little-endian word arithmetic, `MSTORE`/`MLOAD` read-write facts, scratch memory for mapping hashes, selector extraction, calldata decode coupling, mapping-slot keccak facts. Home of the `keccak_size` axiom. |
| `Reach.lean` | The EVM trace layer. `RD` (reached-or-out-of-gas invariant), one forward step lemma per opcode (`RD.<op>`), `CALL`/`STATICCALL` with the callee treated as an opaque `Θ` result, terminal forms `RDret`/`RDrev` with the `reEquiv_*` case builders for `runtimeEquivalenceFor` and the `reEquivElim` eliminators, `Cursor`/`RDc`, and the `evm_run` macro that chains steps with auto-discharged decode/overflow side conditions. |
| `ABI.lean` | Calldata decoding and return-value encoding: per-shape decode lemmas (address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Collapsing chains of memory writes into a canonical form. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `Storage.lean` | Storage maps: red-black-map lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage layout, `accountMapEquiv`/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |
| `Dispatch.lean` | Solm dispatcher facts: `dispatchMsg` as a list walk (`dispatchList`), single-transition instances, `SingleSelectorDispatch`, and the `RDret`/`RDrev.reEquiv*` bridges that connect a finished trace to the equivalence statement. |
| `Dispatcher.lean` | The whole solc selector dispatcher as one driver: `SelTree` (read off the bytecode with `SelTree.readAt`, validated by the `Bool` check `SelTree.check`, semantics `SelTree.lookup`), the entry prefix check `solcEntryCheck` for both selector-load generations, `solcDispatchReachArm` / `solcDispatchNoMatchRevert`, the Solm-side `dispatchMsg_*_of_table` facts from one selector table, and `runtimeEquivalence_of_solcDispatcher`, which assembles the top-level theorem from per-selector `SelectorBody` obligations. |
| `ExternalCall.lean` | The `CALL` ↔ Solm `externalCall` boundary: both sides invoke the same `Θ`, so results coincide (`callCoincides`); transport of call results across equivalent account maps. |
| `Constructor.lean` | Skeletons for constructor (creation-code) equivalence proofs. |

## Dependencies

External: `Ethereum.*` (evmlean — EVM semantics and opcode lemmas), `Solm` (the spec language and
its semantics), `ABI.Decode`, Mathlib (EVMWord and Memory only).

Within `Reasoning/`, imports flow upward:

```
Stepping   EVMWord ── SolmBody
    │         │
    ├── Memory ── MemCascade
    │      │
    │      ├── ABI
    │      └── Reach
    │           │
    └───────── Solc
                │
            Storage
             ├── Dispatch      (also Reach)
             └── ExternalCall  (also SolmBody)

Constructor ← Reach, SolmBody     Initcode ← EVMWord     JumpDest ← (Ethereum only)
Dispatcher ← Solc, Dispatch, SolmBody
```

## Where to look

- Run one opcode of a concrete trace → `Stepping` (`<op>_xstep`), chained via `Reach` (`evm_run`).
- Word arithmetic side condition → `EVMWord`.
- Memory read/write or keccak slot → `Memory` (chains of writes: `MemCascade`).
- Decode calldata / encode a return value → `ABI` (solc-specific length checks: `Solc`).
- A code shape the compiler always emits → `Solc`.
- Storage read/write, packed values, bytes/string layout, account-map equivalence → `Storage`.
- Selector dispatch, connecting a trace to `runtimeEquivalence` → `Dispatch`; the whole dispatcher
  (tree walk, no-match revert, top-level assembly) → `Dispatcher`.
- An external call inside a function body → `ExternalCall` (EVM side: `RD.call` in `Reach`;
  Solm side: `SolmBody`).
- Constructor proofs → `Constructor`, `Initcode`.
- Jump-target validity → `JumpDest`.

## Build

`lake build Reasoning` builds all fifteen files. A bare `lake build` builds only `Solm`
(the default target) — use explicit targets.
