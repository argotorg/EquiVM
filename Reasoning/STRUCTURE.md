# Reasoning/ — structure

Shared, contract-agnostic infrastructure for proving that compiled EVM bytecode refines its Solm
specification. Every per-contract proof in `Examples/` and `Benchmarks/` is assembled from these
files plus contract-specific facts (bytecode literals, selectors, storage layout).

Most declarations are in `Reasoning.Theory`. The EVM trace layer (`RD`, `evm_run`,
`SolcRoutines.lean`, and the `RD.*` lemma halves of `Solc.lean` and `Dispatch.lean`) is in
`Reasoning.Reach`. `SolmArithmetic.lean` includes the nested `Reasoning.Theory.RpowB` and
`Reasoning.Theory.RpowBase` namespaces for the two source-variable conventions.
`JumpDest.lean` has no namespace (it defines a tactic and an attribute).

Some existing helpers use `native_decide`; refactors should not introduce additional axiom
dependencies.

## Files

| File | Contents |
|---|---|
| `Stepping.lean` | Base layer. Trace drivers — `initState` (the fresh EVM state), the `Ξ`-to-iterator bridge (`Xi_*_of_X`), single-step peeling (`X_peel`, `stepContinue`, `stepOOG`, `stepHalt*`) — plus one lemma per opcode (`<op>_xstep`) evaluating a single `Xstep` to an explicit gas-guarded successor state (`st<Op>` definitions). |
| `EVMWord.lean` | `UInt256` arithmetic: no-wrap `toNat` lemmas, bitwise normalization, unsigned comparisons, signed `SLT`, `compare` order instances, the word-rounding used by solc memory allocation. |
| `SolmBody.lean` | The Solm side: `ExecTransitionBody`/`ExecStmt`/`ExecBlock` lemmas. Non-payable guard, call wrappers (external/checked/low-level/delegate), loop rules, block sequencing (`execBlock_append`), locals lookup, storage-access collapse. |
| `Memory.lean` | Byte-level memory: little-endian word arithmetic, `MSTORE`/`MLOAD` read-write facts, scratch memory for mapping hashes, selector extraction, calldata decode coupling, mapping-slot keccak facts, and the `keccak_size` theorem. |
| `Reach.lean` | The EVM trace layer. `RD` (reached-or-out-of-gas invariant), one forward step lemma per opcode (`RD.<op>`), `CALL`/`STATICCALL` with the callee treated as an opaque `Θ` result, terminal forms `RDret`/`RDrev` with the `reEquiv_*` case builders for `runtimeEquivalenceFor` and the `reEquivElim` eliminators, `Cursor`/`RDc`, and the `evm_run` macro that chains steps with auto-discharged decode/overflow side conditions. |
| `ABI.lean` | Calldata decoding and return-value encoding: per-shape decode lemmas (address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Word-write cascades, sparse writes, scratch-memory shapes, and read/size preservation. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `Storage.lean` | Storage maps: `ExtTreeMap` lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage layout, account-map equality/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |
| `Dispatch.lean` | Solm dispatcher facts: `dispatchMsg` as a list walk (`dispatchList`), single-transition instances, `SingleSelectorDispatch`, and the `RDret`/`RDrev.reEquiv*` bridges that connect a finished trace to the equivalence statement. |
| `ExternalCall.lean` | The `CALL` ↔ Solm `externalCall` boundary: both sides invoke the same `Θ`, so results coincide (`callCoincides`); transport of call results across equivalent account maps and substate changes. |
| `Constructor.lean` | Skeletons for constructor (creation-code) equivalence proofs. |
| `WordArithmetic.lean` | Further signed and unsigned word bounds, masks, shifts, rounding, and compiler guard arithmetic. |
| `HeapMemory.lean` | Heap prefixes and cursors, allocation invariants, dynamic tuple and return-data layouts, and dynamic revert payloads. |
| `ABIComposite.lean` | Shared ABI type aliases, strict and legacy scalar-tuple decoders, dynamic-value decoders, and calldata word reads. |
| `ABIViews.lean` | ABI word views, tuple encoders, packed tuple memory and hashes, calldata bounds, selector extraction, and return-value decoding. |
| `PackedStorage.lean` | Packed address, bool, uint8, and uint48 locations, masks, loads, and stores. |
| `StorageLoops.lean` | Index and account-map facts for sequential storage clearing and copying, including prefix composition and repeated stores. |
| `BytecodePatching.lean` | Immutable-word encoding, bytecode splicing, preserved decode windows, and jump destinations. |
| `SolcRoutines.lean` | Bytecode-parameterized getter, authorization, storage-update, checked-arithmetic, and revert routines. |
| `SolmArithmetic.lean` | Source arithmetic expressions, checked and wrapping operations, local-variable frames, and exponentiation-frame evaluation facts. |

## Dependencies

External: `Ethereum.*` (evmlean — EVM semantics and opcode lemmas), `Solm` (the spec language and
its semantics), `ABI.Decode`, and Mathlib.

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
```

The remaining extension modules have distinct responsibilities:

- `ABIComposite` extends `ABI` with tuple and dynamic decoders; `ABIViews` connects those
  encodings to compiler word operations and calldata guards.
- `MemCascade` builds on `Memory`. `Solc` also imports it for scratch-memory layouts;
  `HeapMemory` adds heap invariants and dynamic layouts above `Solc`.
- `PackedStorage` extends `Storage`. `WordArithmetic` supplies the higher-level word bounds
  used by compiler and storage proofs, with `SolmBody` and `Initcode` also available.
- `BytecodePatching` uses `Initcode`, `MemCascade`, and `Solm.Immutables` to connect bytecode
  splices to word writes and preserve decoding.
- `SolcRoutines` combines compiler primitives with heap, packed-storage, and word facts.
- `SolmArithmetic` combines source evaluation, ABI types, and word arithmetic. Its `RpowB`
  and `RpowBase` namespaces retain the two local-variable conventions for exponentiation.
- `StorageLoops` combines storage updates and word arithmetic for clearing and copying loops.

Basic memory bounds and byte-array conversions live in `Memory`; write-cascade facts live in
`MemCascade`; compiler allocation and mapping-memory facts live in `Solc`. State projections
live in `Storage`, code-size/precompile facts in `ExternalCall`, and elementary source evaluation
in `SolmBody`. This keeps those facts beside their definitions instead of collecting them in
separate files by the contract from which they were extracted.

These modules do not import `Examples` or `Benchmarks`. Contract-specific bytecode, selectors,
and storage layouts stay with their proofs. Where a proof is extracted from a concrete source
configuration, the original theorem remains as a specialization of the shared result.

## What belongs in the library

Extend the module that owns the relevant definitions when its dependencies permit it. A new
module should introduce a coherent abstraction or a necessary dependency layer. Before adding
a theorem, look for an existing statement with the same hypotheses and conclusion. Existing
public names for duplicate statements can remain as short applications of one shared proof.

A shared declaration should state a reusable property and have a name that describes that
property independently of its originating contract. For example, an address-word bound or an
ABI tuple encoder belongs here under an address or encoding name. Contract names and names of
individual contract operations should not be used to name shared facts.

Accepting arbitrary words or byte arrays is not sufficient by itself. A lemma can still encode
one contract's concrete memory layout, return buffer, fee constants, or local-variable program.
Keep those specializations in the owning contract directory. In particular:

- `gemJoinCtorDecimalsReturnWrite_size` and `gemJoinCtorDecimalsReturnWrite_read224_32` live in
  `Benchmarks/Dss/GemJoin/ConstructorTraceCall.lean`: the 256-byte buffer and offset 224 describe
  that constructor's decimals call.
- Revert-memory lemmas for particular buffer sizes and free-pointer values stay beside the
  corresponding contract traces. The parameterized memory and revert rules remain shared.
- Fixed decimal values, fee calculations, and the Pow example's concrete loop stay with their
  contract proofs.

Constants dictated by EVM, ABI, or a reusable compiler convention, such as 32-byte words,
160-bit addresses, and ABI field offsets, can appear in shared rules. The distinction is the
source of the constraint and the rule's reuse, rather than the absence of numeric literals.

## Where to look

- Run one opcode of a concrete trace → `Stepping` (`<op>_xstep`), chained via `Reach` (`evm_run`).
- Word arithmetic side condition → `EVMWord`, `WordArithmetic`.
- Memory bounds, byte conversions, and basic read/write facts → `Memory`.
- Write cascades, scratch shapes, and sparse writes → `MemCascade`.
- Compiler memory conventions → `Solc`; heap allocation and dynamic layouts → `HeapMemory`.
- Decode calldata / encode a return value → `ABI`, `ABIComposite`, `ABIViews`.
- A code shape the compiler emits → `Solc`, `SolcRoutines`.
- Storage, state projections, and account-map equality → `Storage`; packed values →
  `PackedStorage`; clearing and copying loops → `StorageLoops`.
- Code-size guards and precompile results → `ExternalCall`.
- Elementary source evaluation → `SolmBody`; arithmetic and exponentiation frames →
  `SolmArithmetic`.
- Immutable bytecode patching and decode preservation → `BytecodePatching`.
- Selector dispatch, connecting a trace to `runtimeEquivalence` → `Dispatch`.
- An external call inside a function body → `ExternalCall` (EVM side: `RD.call` in `Reach`;
  Solm side: `SolmBody`).
- Constructor proofs → `Constructor`, `Initcode`.
- Jump-target validity → `JumpDest`.

## Build

`lake build Reasoning` builds all twenty-three modules. A bare `lake build` builds only `Solm`
(the default target) — use explicit targets.

After changing shared lemmas, check their callers with
`lake build Reasoning Benchmarks Examples EquiVM`.
