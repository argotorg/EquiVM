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
| `Body.lean` | Rewriting lemmas for hand-built derivations: the `Op` monad, frame lookups (`frame_simp`), scalar conversions, `binop`/`unop` on `uint256`/`bool`/`address` (comparisons, checked `+ - * / %` with their `Panic` cases, unchecked wrap), storage slots by location (`readScalar_of_loc`, `writeScalar_of_loc`, `assign_storage_of`; `uint256`, `bool`, `address` at offsets 0 and 1, `bytes32` instances), mappings, dynamic/static array indexing (`storageIndex_*`, `dynArrayLength_of_loc`), `push`/`pop` (`storagePush_some/none`, `storagePop_empty/succ`), `delete` of a `uint256`, struct fields, array lengths, memory objects (`Heap.get?_alloc_*`, `memField_of`, `memIndex_array_*`), event and error argument encoding; literal coercions (`coerce_*`, `implicitConv_literal_u256`), arithmetic with number literals (`unifyInts_u256_lit`, `binop_{add,sub,mul,div,mod}_uint_of_unify`, `binop_*_u256_lit[1]`, `settle_u256_ok/overflow`, `liftArith`), scope exit (`exitScope_*`), struct literals (`structObj_two`), `ofAbi` of fixed bytes and dynamic arrays; packed `uintN` fields at any byte offset (`readScalar_uint_offset[0]`, `writeScalar_uint_packed` with `setPackedWordNat`); memory structs written into storage (`writeStorageDeep_struct`, `writeStructField_*`); ABI types/values of expression results for `abi.encode*`/`keccak256` (`abiTyOfValue_*`, `toAbi_fixedBytes/strLit/memBytes`, `encodePackedValue?_*`, `abiArgsAbi_of_mapM`); explicit conversions (`explicitConv_uint_widen/narrow`, `_uint160_address`, `_address_uint160`, `_address_address`, `_address_contract`, `_contract_address`, `_u256_bytes32`, `_bytes32_u256`, `_literal_address`); shifts, bitwise operators and `**` on `uint256` with typed or literal operands (`binop_shl/shr/bitAnd/bitOr/bitXor_u256[_lit]`, `unop_bitNot_u256`, `exp_u256_ok/overflow`, `binop_exp_u256[_overflow]`, `binop_exp_lit_u256`, `binop_exp_lit_lit`), comparisons with literals (`binop_cmp_u256_lit`), the `Int.toNat`-of-cast helpers (`toNat_natCast_add/sub/mul/pow`, `emod_toNat_of_lt`); mapping keys `uintN`/`bytes32`/`bool`/literal (`storageIndex_mapping_uint/bytes32/bool/u256_lit`), `directMember_*`, `delete` of `bool`/`address` slots and of structs (`clearStorage_bool/address/struct`); environment members (`envMember_value/timestamp/number/chainid/origin`), `bool` slot reads (`readScalar_bool`, `loadIfScalar_bool`); `int256` (`s256Ty/s256Val/s256IntTy`, `settle_s256_ok/overflow`, `unifyInts_s256_*`, `binop_*_sint_of_unify`, `binop_add/sub/mul/div/mod_s256[_overflow]`, comparisons `binop_lt_s256` …, literal operands, `unop_neg_s256[_overflow]`, `unop_neg_lit`, `wrap_s256_of_lt/ge`, `toWord_u256_of_nonneg/neg`, `explicitConv_u256_s256/s256_u256`, `scalarOfAbi_s256`, slots `readScalar/loadIfScalar/writeScalar/writeStorageDeep/assign_storage_s256` on `int256Loc`); `ecrecover` argument encoding (`abiArgs_ecrecover`, `encodeABIValues_ecrecover`), `catch` selection for a parameterless generic clause (`selectCatch_generic_noParams`); `address` slots as values (`accountAddress_ofNat_toNat`, `loadIfScalar_address`, `writeScalar_address'`), scope-exit lookups of absent names (`exitScope_get?_of_none`); `try`/`catch` facts (`decodeRets_single`, `tryRets_single`, `bindTryParams_single`, `ofAbi_scalar_u256/bool/address`, `selectCatch_error/panic/generic_bytes`), call options (`valueOpt_*`, `saltOpt_*`, `saltBytes_bytes32`), memory arrays into storage and `delete` of arrays (`writeStorageDeep_dynArray/array`, `writeElems_eq`, `clearStorage_dynArray/array`, `clearRange_eq`), `abi.decode` facts (`ofAbiList_nil/cons`, `ofAbiStep`, `ofAbi_fold_shift`, `abiTypeOf_*`), packed signed fields (`readScalar_sint_offset`, `writeScalar_sint_packed`). |
| `Dispatch.lean` | The older `RD`-based bridges to the *core* relation (`RDret.specExecutionCore`, …); kept for the ERC20 core proof. |
| `Trace.lean` | The full-relation coupling on `Run`/`Returned`/`Reverted`: `WorldEquiv` (trace world ↔ spec machine, preserved by `SSTORE`/`storeU256`, `SLOAD`, log pushes, external calls with and without value, calls not made for depth or balance), the bridges `Returned.specExecution[W]`, `Reverted.specRevert/specNoDispatch/specDecodingFailed`, `Returned.specCtor[W]`, `Reverted.specCtorRevert/specCtorNonPayable`, `Returned/Reverted.specReceive*`, `specFallback*`; the payload bridges `solcPanicPayload_eq`/`Panic.data_eq`, `solcErrorStringPayload_eq`, `customErrorData_nil/u256`; the exact `LogEntry` of any event with value-type arguments (`mkLogEntry_static` over a `LogArg` list: `address`/`uint256`/`bool`/`bytes32`, any indexed pattern) and the fixed shapes `(address indexed, address indexed, uint256)`, `(address, uint256)`, `(address indexed, address indexed)`, `(bytes32 indexed, address indexed, address indexed)`, and the `abiArgs` encoding of static argument lists (`abiArgs_static`, `abiArgStep`); the general ABI tuple encoding from per-element encodings (`abiHeadTail`, `encodeABIValues?_of_encs`, `encodeABIValue?_string/bytes`, `topicOf_string/bytes`), `string`/`bytes` arguments (`abiArgs_memString/memBytes`) and the `(string)` / `(address indexed, string)` log entries (`mkLogEntry_string`, `mkLogEntry_addr_indexed_string`); dispatcher cases (`Run.dispatchNoMatch`, `Run.solcDispatch{NonPayable,Short,NoMatch}Revert`, `Reverted.specNonPayable/specFallbackNonPayable/specUndispatched`); `decodeArgs_eq`, `ctorPayable_iff_*`, `address_toNat`. |
| `Derivations.lean` | Derivation builders, one per statement/expression shape: `i++`/`++i`/`i--` on locals (`EvalExpr.postIncLocalU256`, …, `ExecPost.postIncLocalU256`), `for` (`ExecStmt.forFinished`), struct literals (`EvalExpr.structLitPlain`), state references (`EvalExpr.stateRef`), `push(v)` (`EvalExpr/ExecStmt.pushValue`), memory indexing (`EvalExpr.indexMemPlain`), `CallFn.plain[Revert]`, internal calls, `msg.sender`, mapping reads/lvalues (one and two levels), `require` (plain and with message), checked `+=`/`-=` on `uint256` slots, plain assignment (locals, `uint256` slots), local declarations, operators (`geU256`, …, `addU256[Overflow]`, …, unchecked forms), `emit` of an `(address,address,uint256)` event, `return` of a scalar, external calls (`externalCallPlain[Failed]`), `transfer`/`send`/`call{value}` with the `(bool, )` destructuring, custom errors (`revertErrorNoArgs`, `revertErrorU256`), loops (`ExecLoop.variant`, `coupledLoop` with the EVM trace), constructors (`ExecInits.storageU256`, `ExecCtorChain.runPlain/topPlain`), modifiers (`ExecChain.modifierNoArgs/modifierPlain`, `placeholder*`, scope bookkeeping), immutables, memory-object members; `abi.encodePacked/encode/encodeWithSelector` (`EvalExpr.abiEncode*Plain`), `keccak256` of memory bytes and of `abi.encodePacked(...)`/`abi.encode(...)` (`EvalExpr.keccakMemBytes/keccakPacked/keccakEncode`), argument lists (`EvalExprs.two/three`); conversions `T(a)` (`EvalExpr.convertPlain`), `type(uintN).max` (`EvalExpr.typeMaxU256/typeMaxUint`); blocks, `unchecked`, `if`, `while`/`for` iterations, `break`/`return`/revert inside loops, `&&`/`||`/`?:` (`ExecStmt.blockNormal/Revert`, `uncheckedNormal/Revert`, `iteTrue/iteFalse[None]`, `whileNormal`, `ExecBlock.one[Revert]`, `ExecLoop.step/stepWhile/exit/breakStep/returnStep/revertStep`, `EvalExpr.andTrue/andFalse/orTrue/orFalse/condTrue/condFalse`); number literals (`EvalExpr.numLit`) and `uint256 op literal` for `+ - * / % < <= > >= == != << >> &` (`EvalExpr.addU256Lit[Overflow]`, `subU256Lit[Underflow]`, `mulU256Lit`, `divU256Lit`, `modU256Lit`, `cmpU256Lit`, `ltU256Lit`, …, `shlU256Lit`, `shrU256Lit`, `bitAndU256Lit`), typed shifts/bitwise/`**` (`shlU256`, `shrU256`, `bitAndU256`, `bitOrU256`, `bitXorU256`, `bitNotU256`, `expU256[Overflow]`, `expLitUint` for `10 ** decimals`, `expLitLit`); mappings with any value-type key (`EvalExpr.mappingIndexScalar`, `EvalLValue.mappingIndex`, `mappingU256U256`, `mappingBytes32U256`, `mappingAddrStruct`, `indexStorageScalar`), storage struct fields (`EvalExpr.storageFieldRead/storageFieldU256`, `EvalLValue.storageField`), `delete` (`ExecStmt.deleteStorageU256/Address/Bool`); number-literal right-hand sides (`ExecStmt.assignStorageU256Lit`, `assignLocalU256Lit`, `varDeclU256Lit`), unchecked `i++` (`EvalExpr/ExecPost.postIncLocalU256Unchecked`), `emit` of any value-type event (`ExecStmt.emitStatic` over a `LogArg` list); environment reads (`EvalExpr.msgValue/blockTimestamp/blockNumber/chainId/txOrigin/thisAddress`), `assert` (`ExecStmt.assertTrue/assertFalse`), `revert("msg")` (`ExecStmt.revertMsg`), tuples and two-value returns (`EvalExpr.tupleTwo`, `ExecStmt.returnTwoU256`), `mapping(address => bool)` reads (`EvalExpr.mappingAddrBool`); `int256` arithmetic, comparisons, negation and casts (`EvalExpr.addS256[Overflow]`, `subS256`, `mulS256`, `divS256`, `ltS256`, `geS256[Lit]`, `negS256`, `negLit`, `convertU256S256`, `convertS256U256`), `int256` state variables and slots (`EvalExpr.stateS256`, `EvalExpr/ExecStmt.assignStorageS256`, `ExecStmt.varDeclS256`); `ecrecover` (`EvalExpr.ecrecoverPlain`, the precompile call as a `callViaEVM` hypothesis), `try recv.f(args) { … } catch { … }` without `returns` (`ExecStmt.tryCallOkNoRets`, `tryCallCaughtGeneric`), `new C(args)` (`EvalExpr.newContractPlain[Failed]`, the creation as a `newViaEVM` hypothesis); value-type state variables (`EvalExpr.stateU256/stateAddress/stateBool`, `EvalLValue.stateVarTy`), `address`/`bool` slot assignments (`EvalExpr/ExecStmt.assignStorageAddress`, `ExecStmt.assignStorageBoolTrue/False`, `assign_storage_address/bool_true/bool_false`); environment reads through a rewritten machine (`EvalExpr.msgSenderEq/msgValueEq/blockTimestampEq`, discharge the equation with `simp` — `storageStore_executionEnv` and `storeU256_executionEnv` are simp lemmas); `try … returns (T x)` (`ExecStmt.tryCallOkOneRet`), typed and parameterised `catch` clauses (`ExecStmt.tryCallCaughtSelected` with `selectCatch_*`), `new C{value}` / `new C{salt}` / `recv.f{value}` (`EvalExpr.newContractValue/newContractSalt/externalCallValue`, `EvalValueOpt.u256`, `EvalSaltOpt.bytes32`), `abi.decode` of memory bytes (`EvalExpr.abiDecodeMemBytes`). |
| `Usage.lean` | Compiled usage examples (no exports): single statements built with the builders (literal arithmetic, keccak of `abi.encodePacked`, mapping writes, custom errors, `unchecked`, `delete`, `emit`) and the whole SimpleAuction `bid()` body as `∃ m', ExecBlock …`. |
| `Strings.lean` | `string`/`bytes` storage on the solc layout: `clearBytesStorage_*`, `writeBytesStorage_*` (short/long, packed/prepared, malformed headers ⇒ `Panic(0x22)`, empty), `readBytesStorage_*`, and the deep read/write/clear of a `string`-typed reference reducing to them. |

## Dependencies

```
Semantics ── Body ── Trace ── Derivations
                │      │
                │      └── Equiv, EVMReasoning.SolcIdioms, Ethereum.Theory.StorageExtensionality
                ├── Strings
                └── Dispatch (Equiv, EVMReasoning.Reach)
```

`Trace`, `Derivations`, `Strings` and `Usage` are in the `Solidity` umbrella (CI); `Dispatch` and `Body`
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

## Reduction footgun

`settle`, `IntTy.inRange`, `IntTy.max` must never be unfolded (by `simp`, `dsimp`, `rfl`, `decide`
or a `match` reduction that `whnf`s its discriminant) on an operand containing a numeral, e.g.
`add uint256 true (↑n) 1`: `whnf` of `Int.decLe` against `2 ^ 256 - 1` recurses through
`Nat.sub` on the literal and overflows the elaborator ("maximum recursion depth") or the kernel
("deep recursion detected").  Symbolic operands (`↑a + ↑b`) are safe.  Eliminate `binop` on
literals with `binop_*_uint_of_unify` + `unifyInts_u256_lit` + `settle_u256_ok/overflow` (all
proved on variables) and rewrite with them; never `simp [binop, …]` on a goal with a literal.

## Usage idioms (exercised in `Usage.lean`)

- A local read as a typed value: `hval ▸ EvalExpr.local (m := m) hx` (the machine is not inferable
  from `hx`), or `EvalExpr.localVal ty loc h` with the binding spelled out.
- `ExecStmt.emitStatic xs …` yields `topics`/`data` as `filter`/`map`/`flatMap` over the literal
  `LogArg` list: finish with `simpa [LogVal.word, LogVal.bytes] using h`; its `hwf` is `by simp <;> omega`.
- Comparison builders return `.bool (decide p)`: rewrite with `decide_eq_true h` before `iteTrue`
  or `requireTrue`.
- A whole body with an unknown final machine: prove `∃ m', ExecBlock … (.normal fr' m')` by
  `constructor` and a chain of `refine ExecBlock.cons (…) ?_` (see `Usage.lean`, SimpleAuction `bid`).
  After an `if { … }` block the frame is `fr.exitScope fr`; re-derive the `get? = none` facts with
  `exitScope_get?_of_none`.
- `storeU256`/`storageStore` are opaque to definitional unfolding (`storageStore` matches on the
  account lookup): after stores, `msg.sender`/`msg.value` must be read with the `*Eq` builders
  and `by simp`, not with `EvalExpr.msgSender` expected at the original machine.
- `EvalExpr.blockTimestamp` yields `wordNat ts`, i.e. `u256Val (EVM.Word.ofNat ts).toNat`.
- Results of storage writes are stated with `storeU256 m slot w`; a hand-written structure update
  `{ m with evm := … }` must keep continuation lines indented past the field.

## Not covered yet

Events with array arguments and multi-element dynamic layouts beyond the `(string)` shapes (the
general `encodeABIValues?_of_encs` gives the bytes, the `mkLogEntry_*` instance is per shape); the
round trip `errorStringArg? cfg (errorStringData s) = some s` (needs an ABI string decode lemma);
`try` with several `returns`; the EVM-side `CREATE` step lemma for `new`; tuples beyond `(bool, )` and
pairs of `uint256`; immutables beyond reads (`immStore`/`runtimeCodeOf`); `int256` beyond width 256 and packed signed fields; the EVM-side shapes of `push`/`pop`
and `receive`/`fallback` dispatch (no example bytecode fixes them yet); custom errors with more than
one argument or non-word arguments (`Run.solcCustomErrorRevertU256` covers `revert E(x)` with one word
argument in the inline-encoder shape of solc's SimpleAuction output).
