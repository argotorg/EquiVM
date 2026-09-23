# Solidity/Theory/ — structure

Proof infrastructure for the Solidity spec language: the interpreter/rules equivalence, and the
coupling of `solidityExec` derivations with EVM traces (`EVMReasoning/Trace.lean` and its solc
shape lemmas) into the refinement relation of `Solidity/Equiv.lean`.  Everything is in namespace
`Solidity`.  Nothing here mentions a particular contract; per-contract proofs supply the pinned
bytecode, its selector/jump-destination facts, the storage layout facts and the keccak facts.

## Files

| File | Contents |
|---|---|
| `InterpLemmas.lean`, `Sound/*.lean`, `Sound.lean`, `InterpSound.lean`, `Complete.lean`, `InterpEquiv.lean` | The fuel interpreter agrees with the relational rules: soundness, completeness (`Complete.lean` is generated), determinism, `solidityExec_iff`. |
| `Body.lean` | Rewriting lemmas for hand-built derivations: the `Op` monad, frame lookups (`frame_simp`), scalar conversions, `binop`/`unop` on `uint256`/`bool`/`address` (comparisons, checked `+ - * / %` with their `Panic` cases, unchecked wrap), storage slots by location (`readScalar_of_loc`, `writeScalar_of_loc`, `assign_storage_of`; `uint256`, `bool`, `address` at offsets 0 and 1, `bytes32` instances), mappings, dynamic/static array indexing (`storageIndex_*`, `dynArrayLength_of_loc`), `push`/`pop` (`storagePush_some/none`, `storagePop_empty/succ`), `delete` of a `uint256`, struct fields, array lengths, memory objects (`Heap.get?_alloc_*`, `memField_of`, `memIndex_array_*`), event and error argument encoding. |
| `Dispatch.lean` | The older `RD`-based bridges to the *core* relation (`RDret.specExecutionCore`, …); kept for the ERC20 core proof. |
| `Trace.lean` | The full-relation coupling on `Run`/`Returned`/`Reverted`: `WorldEquiv` (trace world ↔ spec machine, preserved by `SSTORE`/`storeU256`, `SLOAD`, log pushes, external calls with and without value, calls not made for depth or balance), the bridges `Returned.specExecution[W]`, `Reverted.specRevert/specNoDispatch/specDecodingFailed`, `Returned.specCtor[W]`, `Reverted.specCtorRevert/specCtorNonPayable`, `Returned/Reverted.specReceive*`, `specFallback*`; the payload bridges `solcPanicPayload_eq`/`Panic.data_eq`, `solcErrorStringPayload_eq`, `customErrorData_nil/u256`; the exact `LogEntry` of `(address indexed, address indexed, uint256)`, `(address, uint256)`, `(address indexed, address indexed)` and `(bytes32 indexed, address indexed, address indexed)` events; dispatcher cases (`Run.dispatchNoMatch`, `Run.solcDispatch{NonPayable,Short,NoMatch}Revert`, `Reverted.specNonPayable/specFallbackNonPayable/specUndispatched`); `decodeArgs_eq`, `ctorPayable_iff_*`, `address_toNat`. |
| `Derivations.lean` | Derivation builders, one per statement/expression shape: `CallFn.plain[Revert]`, internal calls, `msg.sender`, mapping reads/lvalues (one and two levels), `require` (plain and with message), checked `+=`/`-=` on `uint256` slots, plain assignment (locals, `uint256` slots), local declarations, operators (`geU256`, …, `addU256[Overflow]`, …, unchecked forms), `emit` of an `(address,address,uint256)` event, `return` of a scalar, external calls (`externalCallPlain[Failed]`), `transfer`/`send`/`call{value}` with the `(bool, )` destructuring, custom errors (`revertErrorNoArgs`, `revertErrorU256`), loops (`ExecLoop.variant`, `coupledLoop` with the EVM trace), constructors (`ExecInits.storageU256`, `ExecCtorChain.runPlain/topPlain`), modifiers (`ExecChain.modifierNoArgs/modifierPlain`, `placeholder*`, scope bookkeeping), immutables, memory-object members. |
| `Strings.lean` | `string`/`bytes` storage on the solc layout: `clearBytesStorage_*`, `writeBytesStorage_*` (short/long, packed/prepared, malformed headers ⇒ `Panic(0x22)`, empty), `readBytesStorage_*`, and the deep read/write/clear of a `string`-typed reference reducing to them. |

## Dependencies

```
Semantics ── Body ── Trace ── Derivations
                │      │
                │      └── Equiv, EVMReasoning.SolcIdioms, Ethereum.Theory.StorageExtensionality
                ├── Strings
                └── Dispatch (Equiv, EVMReasoning.Reach)
```

`Trace`, `Derivations` and `Strings` are in the `Solidity` umbrella (CI); `Dispatch` and `Body`
are built through the ERC20 example.

## Where to look

- A whole message call or deployment → `Trace.lean` (`Returned.specExecutionW` with a `WorldEquiv`
  built from `WorldEquiv.init` and threaded through `sstore`/`pushLog`/`callMade`).
- A revert's exact bytes → `Trace.lean` (`Panic.data_eq`, `solcErrorStringPayload_eq`, the
  `ByteArray.empty` dispatcher cases).
- One statement or expression of a body → `Derivations.lean`; the pure facts it needs
  (`binop`, `readScalar`, `storageIndex`, …) → `Body.lean`.
- `string`/`bytes` state variables → `Strings.lean`.
- Calldata decoding → `EVMReasoning/ABI.lean` through `decodeArgs_eq`.

## Not covered yet

Events with non-value-type arguments; `try/catch`, `new`, `delete` of non-string reference types,
memory struct/array literals and writes, tuples beyond `(bool, )`, `abi.encode*`, `keccak256`,
`ecrecover`; immutables beyond reads (`immStore`/`runtimeCodeOf`); packed `uintN` fields
(`N < 256`); the EVM-side shapes of `push`/`pop`, `receive`/`fallback` dispatch and the
one-argument custom-error encoder (the pieces `Run.solcErrorSelectorStore`, `errorSelectorArgMem_read36`
and `Run.solcRevertBlock` exist in `EVMReasoning/SolcIdioms.lean`, the encoder segment is per contract).
