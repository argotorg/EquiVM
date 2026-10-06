# Reasoning/ — structure

Shared, contract-agnostic infrastructure for proving that compiled EVM bytecode refines its Solm
specification. Every per-contract proof in `Examples/` and `Benchmarks/` is assembled from these
files plus contract-specific facts (bytecode literals, selectors, storage layout).

Most declarations are in `Reasoning.Theory`. The EVM trace layer (`RD`, `evm_run`,
`SolcRoutines.lean`, and the `RD.*` lemma halves of `Solc.lean` and `Dispatch.lean`) is in
`Reasoning.Reach`. `SolmRpow.lean` uses the nested `Reasoning.Theory.RpowB` and
`Reasoning.Theory.RpowBase` namespaces for the two source-variable conventions.
`JumpDest.lean` has no namespace (it defines a tactic and an attribute).

The shared reasoning library introduces no axioms.

## Files

| File | Contents |
|---|---|
| `Stepping.lean` | Base layer. Trace drivers — `initState` (the fresh EVM state), the `Ξ`-to-iterator bridge (`Xi_*_of_X`), single-step peeling (`X_peel`, `stepContinue`, `stepOOG`, `stepHalt*`) — plus one lemma per opcode (`<op>_xstep`) evaluating a single `Xstep` to an explicit gas-guarded successor state (`st<Op>` definitions). |
| `EVMWord.lean` | `UInt256` arithmetic: no-wrap `toNat` lemmas, bitwise normalization, unsigned comparisons, signed `SLT`, `compare` order instances, the word-rounding used by solc memory allocation. |
| `SolmBody.lean` | The Solm side: `ExecTransitionBody`/`ExecStmt`/`ExecBlock` lemmas. Non-payable guard, call wrappers (external/checked/low-level/delegate), loop rules, block sequencing (`execBlock_append`), locals lookup, storage-access collapse. |
| `Memory.lean` | Byte-level memory: little-endian word arithmetic, `MSTORE`/`MLOAD` read-write facts, scratch memory for mapping hashes, selector extraction, calldata decode coupling, mapping-slot keccak facts, and the `keccak_size` theorem. |
| `Reach.lean` | The EVM trace layer. `RD` (reached-or-out-of-gas invariant), one forward step lemma per opcode (`RD.<op>`), `CALL`/`STATICCALL` with the callee treated as an opaque `Θ` result, terminal forms `RDret`/`RDrev` with the `reEquiv_*` case builders for `runtimeEquivalenceFor` and the `reEquivElim` eliminators, `Cursor`/`RDc`, and the `evm_run` macro that chains steps with auto-discharged decode/overflow side conditions. |
| `ABI.lean` | Calldata decoding and return-value encoding: per-shape decode lemmas (address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Collapsing chains of memory writes into a canonical form. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `Storage.lean` | Storage maps: `ExtTreeMap` lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage layout, account-map equality/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |
| `Dispatch.lean` | Solm dispatcher facts: `dispatchMsg` as a list walk (`dispatchList`), single-transition instances, `SingleSelectorDispatch`, and the `RDret`/`RDrev.reEquiv*` bridges that connect a finished trace to the equivalence statement. |
| `ExternalCall.lean` | The `CALL` ↔ Solm `externalCall` boundary: both sides invoke the same `Θ`, so results coincide (`callCoincides`); transport of call results across equivalent account maps and substate changes. |
| `Constructor.lean` | Skeletons for constructor (creation-code) equivalence proofs. |
| `WordArithmetic.lean` | Further signed and unsigned word bounds, masks, shifts, rounding, and compiler guard arithmetic. |
| `HeapMemory.lean` | Memory prefixes and cursors, sparse writes, copying, and return-data memory. |
| `DynamicMemory.lean` | Dynamic byte-array memory, padding, copying, and revert-data layouts. |
| `MemoryShapes.lean` | Reusable single-word, two-word, and error-string memory shapes, with read, size, preservation, and hash facts. |
| `SolcMemory.lean` | Compiler memory facts combining shared memory shapes with solc allocation and mapping conventions. |
| `MemoryArithmetic.lean` | Memory-size and gas bounds, byte-array conversions, copy results, and write-cascade facts. |
| `ABILegacy.lean` | Legacy solc ABI scalar encoders and decoders, including padded word handling. |
| `ABIComposite.lean` | Shared ABI type aliases, tuple and dynamic-value encodings, and strict and legacy decoding facts. |
| `ABIViews.lean` | ABI word views, tuple encoders, packed tuple memory and hashes, calldata bounds, selector extraction, and return-value decoding. |
| `PackedStorage.lean` | Packed address, bool, uint8, and uint48 locations, masks, loads, and stores. |
| `StateFacts.lean` | Account and storage projections, state equality, external-code and precompile facts, and elementary source evaluation. |
| `StorageLoops.lean` | Index and account-map facts for sequential storage clearing and copying. |
| `BytecodePatching.lean` | Immutable-word encoding, bytecode splicing, preserved decode windows, and jump destinations. |
| `SolcRoutines.lean` | Bytecode-parameterized getter, authorization, storage-update, checked-arithmetic, and revert routines. |
| `SolmArithmetic.lean` | Source arithmetic expressions, checked and wrapping operations, and shared local-variable frames. |
| `SolmRpow.lean` | Exponentiation local-variable frames and their contract-independent evaluation facts. |

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

The additional modules build on that core:

- `PackedStorage` builds on `Storage`; `WordArithmetic` also uses `SolmBody` and `Initcode`.
- `MemoryShapes` builds on `MemCascade`; `SolcMemory`, `HeapMemory`, and `DynamicMemory`
  also use `Solc`.
- `ABILegacy` builds on `ABI`, and `ABIComposite` builds on `ABILegacy`.
- `BytecodePatching` uses `Initcode`, `Memory`, and `Solm.Immutables`.
- `MemoryArithmetic` combines the memory, word, patching, and composite ABI facts.
  `ABIViews` builds on this layer.
- `StateFacts` combines `ExternalCall`, `WordArithmetic`, and `MemoryArithmetic`;
  `StorageLoops` builds on `StateFacts`.
- `SolcRoutines` combines `Solc` with packed-storage, memory-shape, and memory-arithmetic facts.
- `SolmArithmetic` builds on `SolmBody` and `ABI`; `SolmRpow` also uses `WordArithmetic`.

These modules do not import `Examples` or `Benchmarks`. Contract-specific bytecode, selectors,
and storage layouts stay with their proofs. Where a proof is extracted from a concrete source
configuration, the original theorem remains as a specialization of the shared result.

## What belongs in the library

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
- Memory read/write or keccak slot → `Memory`, `MemoryShapes`, `SolcMemory`;
  chains of writes → `MemCascade`; copy and size bounds → `MemoryArithmetic`.
- Decode calldata / encode a return value → `ABI`, `ABILegacy`, `ABIComposite`, `ABIViews`.
- A code shape the compiler always emits → `Solc`, `SolcRoutines`.
- Storage read/write, packed values, bytes/string layout, account-map equality → `Storage`,
  `PackedStorage`, `StateFacts`; clearing and copying loops → `StorageLoops`.
- Source arithmetic and local-variable frames → `SolmArithmetic`, `SolmRpow`.
- Immutable bytecode patching and decode preservation → `BytecodePatching`.
- Selector dispatch, connecting a trace to `runtimeEquivalence` → `Dispatch`.
- An external call inside a function body → `ExternalCall` (EVM side: `RD.call` in `Reach`;
  Solm side: `SolmBody`).
- Constructor proofs → `Constructor`, `Initcode`.
- Jump-target validity → `JumpDest`.

## Build

`lake build Reasoning` builds all thirty modules. A bare `lake build` builds only `Solm`
(the default target) — use explicit targets.

After changing shared lemmas, check their callers with
`lake build Reasoning Benchmarks Examples EquiVM`.
