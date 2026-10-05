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
| `Body.lean` | Rewriting lemmas for hand-built derivations: the `Op` monad, frame lookups (`frame_simp`), scalar conversions, `binop`/`unop` on `uint256`/`bool`/`address` (comparisons, checked `+ - * / %` with their `Panic` cases, unchecked wrap), storage slots by location (`readScalar_of_loc`, `writeScalar_of_loc`, `assign_storage_of`; `uint256`, `bool`, `address` at offsets 0 and 1, `bytes32` instances), mappings, dynamic/static array indexing (`storageIndex_*`, `dynArrayLength_of_loc`), `push`/`pop` (`storagePush_some/none`, `storagePop_empty/succ`), `delete` of a `uint256`, struct fields, array lengths, memory objects (`Heap.get?_alloc_*`, `memField_of`, `memIndex_array_*`), event and error argument encoding; literal coercions (`coerce_*`, `implicitConv_literal_u256`), arithmetic with number literals (`unifyInts_u256_lit`, `binop_{add,sub,mul,div,mod}_uint_of_unify`, `binop_*_u256_lit[1]`, `settle_u256_ok/overflow`, `liftArith`), scope exit (`exitScope_*`), struct literals (`structObj_two`), `ofAbi` of fixed bytes and dynamic arrays; packed `uintN` fields at any byte offset (`readScalar_uint_offset[0]`, `writeScalar_uint_packed` with `setPackedWordNat`); memory structs written into storage (`writeStorageDeep_struct`, `writeStructField_*`); ABI types/values of expression results for `abi.encode*`/`keccak256` (`abiTyOfValue_*`, `toAbi_fixedBytes/strLit/memBytes`, `encodePackedValue?_*`, `abiArgsAbi_of_mapM`); explicit conversions (`explicitConv_uint_widen/narrow`, `_uint160_address`, `_address_uint160`, `_address_address`, `_address_contract`, `_contract_address`, `_u256_bytes32`, `_bytes32_u256`, `_literal_address`); shifts, bitwise operators and `**` on `uint256` with typed or literal operands (`binop_shl/shr/bitAnd/bitOr/bitXor_u256[_lit]`, `unop_bitNot_u256`, `exp_u256_ok/overflow`, `binop_exp_u256[_overflow]`, `binop_exp_lit_u256`, `binop_exp_lit_lit`), comparisons with literals (`binop_cmp_u256_lit`), the `Int.toNat`-of-cast helpers (`toNat_natCast_add/sub/mul/pow`, `emod_toNat_of_lt`); mapping keys `uintN`/`bytes32`/`bool`/literal (`storageIndex_mapping_uint/bytes32/bool/u256_lit`), `directMember_*`, `delete` of `bool`/`address` slots and of structs (`clearStorage_bool/address/struct`); environment members (`envMember_value/timestamp/number/chainid/origin`), `bool` slot reads (`readScalar_bool`, `loadIfScalar_bool`); `int256` (`s256Ty/s256Val/s256IntTy`, `settle_s256_ok/overflow`, `unifyInts_s256_*`, `binop_*_sint_of_unify`, `binop_add/sub/mul/div/mod_s256[_overflow]`, comparisons `binop_lt_s256` …, literal operands, `unop_neg_s256[_overflow]`, `unop_neg_lit`, `wrap_s256_of_lt/ge`, `toWord_u256_of_nonneg/neg`, `explicitConv_u256_s256/s256_u256`, `scalarOfAbi_s256`, slots `readScalar/loadIfScalar/writeScalar/writeStorageDeep/assign_storage_s256` on `int256Loc`); `ecrecover` argument encoding (`abiArgs_ecrecover`, `encodeABIValues_ecrecover`), `catch` selection for a parameterless generic clause (`selectCatch_generic_noParams`); `address` slots as values (`accountAddress_ofNat_toNat`, `loadIfScalar_address`, `writeScalar_address'`), scope-exit lookups of absent names (`exitScope_get?_of_none`); `try`/`catch` facts (`decodeRets_single`, `tryRets_single`, `bindTryParams_single`, `ofAbi_scalar_u256/bool/address`, `selectCatch_error/panic/generic_bytes`), call options (`valueOpt_*`, `saltOpt_*`, `saltBytes_bytes32`), memory arrays into storage and `delete` of arrays (`writeStorageDeep_dynArray/array`, `writeElems_eq`, `clearStorage_dynArray/array`, `clearRange_eq`), `abi.decode` facts (`ofAbiList_nil/cons`, `ofAbiStep`, `ofAbi_fold_shift`, `abiTypeOf_*`), packed signed fields (`readScalar_sint_offset`, `writeScalar_sint_packed`); `declare_u256/bool/address/bytes32`, `assign_local_bool/address/uint`, decoded returns of any arity (`decodeRets_eq_ofAbiList`, `decodeRets_of_ofAbiList`, `tryRets_of_ofAbiList`, `bindTryParams_cons`; `decodeRets_two`, `tryRets_two`, `bindTryParams_two` as fixed-arity shortcuts); integers of any width (`settle_uint_ok/overflow_hi/overflow_lo`, `settle_sint_ok/overflow`, `unifyInts_uint_uint/widen/widen'/lit`, `unifyInts_sint_sint`, `binop_add/sub/mul/div/mod_uint[_overflow/_underflow]`, `binop_lt/le/gt/ge/eq/ne_uint`, `binop_add/sub/mul_sint`, `binop_lt_sint`, `scalarOfAbi_uint_lt`). |
| `Trace.lean` | The full-relation coupling on `Run`/`Returned`/`Reverted`: `WorldEquiv` (trace world ↔ spec machine, preserved by `SSTORE`/`storeU256`, `SLOAD`, log pushes, external calls with and without value, calls not made for depth or balance), the bridges `Returned.specExecution[W]`, `Reverted.specRevert/specNoDispatch/specDecodingFailed`, `Returned.specCtor[W]`, `Reverted.specCtorRevert/specCtorNonPayable`, `Returned/Reverted.specReceive*`, `specFallback*`; the payload bridges `solcPanicPayload_eq`/`Panic.data_eq`, `solcErrorStringPayload_eq`, `customErrorData_nil/u256`; the exact `LogEntry` of any event with value-type arguments (`mkLogEntry_static` over a `LogArg` list: `address`/`uint256`/`bool`/`bytes32`, any indexed pattern) and the fixed shapes `(address indexed, address indexed, uint256)`, `(address, uint256)`, `(address indexed, address indexed)`, `(bytes32 indexed, address indexed, address indexed)`, and the `abiArgs` encoding of static argument lists (`abiArgs_static`, `abiArgStep`); the general ABI tuple encoding from per-element encodings (`abiHeadTail`, `encodeABIValues?_of_encs`, `encodeABIValue?_string/bytes`, `topicOf_string/bytes`), `string`/`bytes` arguments (`abiArgs_memString/memBytes`) and the `(string)` / `(address indexed, string)` log entries (`mkLogEntry_string`, `mkLogEntry_addr_indexed_string`); arrays of static elements (`encodeABIStaticArrayElems?_of_encs`, `encodeABIArrayElems?_static`, `encodeABIValue?_dynArray_static/array_static`, `topicOf_dynArray_static`, the `uint256[]` instances `encodeABIValue?_dynArray_u256`, `abiArgs_memArray_u256`, `mkLogEntry_u256Array`); dispatcher cases (`Run.dispatchNoMatch`, `Run.solcDispatch{NonPayable,Short,NoMatch}Revert`, `Reverted.specNonPayable/specFallbackNonPayable/specUndispatched`); `decodeArgs_eq`, `ctorPayable_iff_*`, `address_toNat`. |
| `Derivations.lean` | Derivation builders, one per statement/expression shape: `i++`/`++i`/`i--` on locals (`EvalExpr.postIncLocalU256`, …, `ExecPost.postIncLocalU256`), `for` (`ExecStmt.forFinished`), struct literals (`EvalExpr.structLitPlain`), state references (`EvalExpr.stateRef`), `push(v)` (`EvalExpr/ExecStmt.pushValue`), memory indexing (`EvalExpr.indexMemPlain`), `CallFn.plain[Revert]`, internal calls, `msg.sender`, mapping reads/lvalues (one and two levels), `require` (plain and with message), checked `+=`/`-=` on `uint256` slots, plain assignment (locals, `uint256` slots), local declarations, operators (`geU256`, …, `addU256[Overflow]`, …, unchecked forms), `emit` of an `(address,address,uint256)` event, `return` of a scalar, external calls (`externalCallPlain[Failed]`), `transfer`/`send`/`call{value}` with the `(bool, )` destructuring, custom errors (`revertErrorNoArgs`, `revertErrorU256`), loops (`ExecLoop.variant`, `coupledLoop` with the EVM trace), constructors (`ExecInits.storageU256`, `ExecCtorChain.runPlain/topPlain`), modifiers (`ExecChain.modifierNoArgs/modifierPlain`, `placeholder*`, scope bookkeeping), immutables, memory-object members; `abi.encodePacked/encode/encodeWithSelector` (`EvalExpr.abiEncode*Plain`), `keccak256` of memory bytes and of `abi.encodePacked(...)`/`abi.encode(...)` (`EvalExpr.keccakMemBytes/keccakPacked/keccakEncode`), argument lists (`EvalExprs.two/three`); conversions `T(a)` (`EvalExpr.convertPlain`), `type(uintN).max` (`EvalExpr.typeMaxU256/typeMaxUint`); blocks, `unchecked`, `if`, `while`/`for` iterations, `break`/`return`/revert inside loops, `&&`/`||`/`?:` (`ExecStmt.blockNormal/Revert`, `uncheckedNormal/Revert`, `iteTrue/iteFalse[None]`, `whileNormal`, `ExecBlock.one[Revert]`, `ExecLoop.step/stepWhile/exit/breakStep/returnStep/revertStep`, `EvalExpr.andTrue/andFalse/orTrue/orFalse/condTrue/condFalse`); number literals (`EvalExpr.numLit`) and `uint256 op literal` for `+ - * / % < <= > >= == != << >> &` (`EvalExpr.addU256Lit[Overflow]`, `subU256Lit[Underflow]`, `mulU256Lit`, `divU256Lit`, `modU256Lit`, `cmpU256Lit`, `ltU256Lit`, …, `shlU256Lit`, `shrU256Lit`, `bitAndU256Lit`), typed shifts/bitwise/`**` (`shlU256`, `shrU256`, `bitAndU256`, `bitOrU256`, `bitXorU256`, `bitNotU256`, `expU256[Overflow]`, `expLitUint` for `10 ** decimals`, `expLitLit`); mappings with any value-type key (`EvalExpr.mappingIndexScalar`, `EvalLValue.mappingIndex`, `mappingU256U256`, `mappingBytes32U256`, `mappingAddrStruct`, `indexStorageScalar`), storage struct fields (`EvalExpr.storageFieldRead/storageFieldU256`, `EvalLValue.storageField`), `delete` (`ExecStmt.deleteStorageU256/Address/Bool`); number-literal right-hand sides (`ExecStmt.assignStorageU256Lit`, `assignLocalU256Lit`, `varDeclU256Lit`), unchecked `i++` (`EvalExpr/ExecPost.postIncLocalU256Unchecked`), `emit` of any value-type event (`ExecStmt.emitStatic` over a `LogArg` list); environment reads (`EvalExpr.msgValue/blockTimestamp/blockNumber/chainId/txOrigin/thisAddress`), `assert` (`ExecStmt.assertTrue/assertFalse`), `revert("msg")` (`ExecStmt.revertMsg`), tuples and two-value returns (`EvalExpr.tupleTwo`, `ExecStmt.returnTwoU256`), `mapping(address => bool)` reads (`EvalExpr.mappingAddrBool`); `int256` arithmetic, comparisons, negation and casts (`EvalExpr.addS256[Overflow]`, `subS256`, `mulS256`, `divS256`, `ltS256`, `geS256[Lit]`, `negS256`, `negLit`, `convertU256S256`, `convertS256U256`), `int256` state variables and slots (`EvalExpr.stateS256`, `EvalExpr/ExecStmt.assignStorageS256`, `ExecStmt.varDeclS256`); `ecrecover` (`EvalExpr.ecrecoverPlain`, the precompile call as a `callViaEVM` hypothesis), `try recv.f(args) { … } catch { … }` without `returns` (`ExecStmt.tryCallOkNoRets`, `tryCallCaughtGeneric`), `new C(args)` (`EvalExpr.newContractPlain[Failed]`, the creation as a `newViaEVM` hypothesis); value-type state variables (`EvalExpr.stateU256/stateAddress/stateBool`, `EvalLValue.stateVarTy`), `address`/`bool` slot assignments (`EvalExpr/ExecStmt.assignStorageAddress`, `ExecStmt.assignStorageBoolTrue/False`, `assign_storage_address/bool_true/bool_false`); environment reads through a rewritten machine (`EvalExpr.msgSenderEq/msgValueEq/blockTimestampEq`, discharge the equation with `simp` — `storageStore_executionEnv` and `storeU256_executionEnv` are simp lemmas); `try … returns (T x)` (`ExecStmt.tryCallOkOneRet`), typed and parameterised `catch` clauses (`ExecStmt.tryCallCaughtSelected` with `selectCatch_*`), `new C{value}` / `new C{salt}` / `recv.f{value}` (`EvalExpr.newContractValue/newContractSalt/externalCallValue`, `EvalValueOpt.u256`, `EvalSaltOpt.bytes32`), `abi.decode` of memory bytes (`EvalExpr.abiDecodeMemBytes`); tuples (`ExecStmt.tupleDeclTwo/Three/SkipMiddle/TwoU256`, `EvalExpr/ExecStmt.assignTupleTwo`, `assignTupleFirst`, `assignTupleTwoLocalsU256`, `ExecStmt.returnTwo/returnThree`, `EvalExpr.tupleThree`); `try … returns (…)` of any arity (`ExecStmt.tryCallOkRets` with `ofAbiList_cons`/`bindTryParams_cons`; `tryCallOkOneRet`, `tryCallOkTwoRets` as shortcuts); builtins and members (`EvalExpr.addmodU256/mulmodU256/gasleftVal/msgDataVal/addressBalance/bytesNLength/storageArrayLength/enumConst/constVarVal/contractCast/arrayLitPlain/newArrayPlain`); `push()`/`pop()` (`EvalExpr.pushEmpty/popLast/popEmptyPanic`); `require(c, Err())`, `revert()`, `return;` (`ExecStmt.requireCustomNoArgs/revertEmptyStmt/returnNoneStmt`); `do … while`, `continue`, `for` without init, `continue` iterations (`ExecStmt.doWhileNormal/continueStmt/forNoInitNormal`, `ExecLoop.stepContinue`); `super`/base/library/`using for` calls and `delegatecall` (`EvalExpr.superCallPlain/baseCallPlain/libraryCallPlain/usingForCallPlain/delegateCallPlain`), calls to code-less addresses (`externalCallNoCodePlain`), `try new` (`ExecStmt.tryNewOkNoRets/tryNewCaughtGeneric`), uncaught `try` reverts (`tryCallUncaughtPlain`), `abi.encodeWithSignature` (`EvalExpr.abiEncodeWithSignaturePlain`), `delete` of a local (`ExecStmt.deleteLocalU256`); integers of any width (`EvalExpr.addUint[Overflow]/subUint/mulUint/divUint/ltUint/eqUint/addSint`, casts `convertNarrow/convertWiden`); immutables in constructors (`ExecStmt.assignImmutableU256/Address`, `EvalExpr.immutableLocalVal`). |
| `Usage.lean` | Compiled usage examples (no exports): single statements built with the builders (literal arithmetic, keccak of `abi.encodePacked`, mapping writes, custom errors, `unchecked`, `delete`, `emit`) and the whole SimpleAuction `bid()` body as `∃ m', ExecBlock …`. |
| `Strings.lean` | `string`/`bytes` storage on the solc layout: `clearBytesStorage_*`, `writeBytesStorage_*` (short/long, packed/prepared, malformed headers ⇒ `Panic(0x22)`, empty), `readBytesStorage_*`, and the deep read/write/clear of a `string`-typed reference reducing to them. |

## Dependencies

```
Semantics ── Body ── Trace ── Derivations
                │      │
                │      └── Equiv, EVMReasoning.SolcIdioms, Ethereum.Theory.StorageExtensionality
                └── Strings
```

`Body`, `Trace`, `Derivations`, `Strings` and `Usage` are in the `Solidity` umbrella (CI).  There is
one refinement relation (`Solidity/Equiv.lean`: accounts, return data, exact revert data, logs).

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
  `exitScope_get?_of_none`, the others with `exitScope_get?` (see the "Scopes" examples).
- `storeU256`/`storageStore` are opaque to definitional unfolding (`storageStore` matches on the
  account lookup): after stores, `msg.sender`/`msg.value` must be read with the `*Eq` builders
  and `by simp`, not with `EvalExpr.msgSender` expected at the original machine.
- `EvalExpr.blockTimestamp` yields `wordNat ts`, i.e. `u256Val (EVM.Word.ofNat ts).toNat`.
- Results of storage writes are stated with `storeU256 m slot w`; a hand-written structure update
  `{ m with evm := … }` must keep continuation lines indented past the field.

## Semantics additions of 2026-10-02 and their facts

Named arguments on every call form (`callArgs`; `callArgs_positional`, `callArgs_named`), free
functions (`FlatContract.fnsNamed_vtable/free`), `C.f.selector` / `this.f.selector`
(`fnRefContract_this/ident`, `selectorMember_of_unique`, `EvalExpr.selectorVal`), `address.code`
as `bytes memory` (`allocBytes_eq`, `memLength_allocBytes`, `codeSize_eq`, `EvalExpr.codeLength`),
exact literal arithmetic (inexact literal division has no derivation; units apply before the
decimal point).  `directMember` is now true on function references, so `directMember_member`
needs `fnRefContract fc fr e = none` (`fnRefContract_index/member/call` are simp lemmas,
`fnRefContract_ident_local/env/var/noContract` take the discharging facts).

Added 2026-10-03: overloaded events (`emit` resolves among `fc.eventsNamed ev` by the evaluated
arguments: `eventArgs`, `resolveEvent`, `eventFits`; `resolveEvent_single`, `eventFits_static`,
`eventFits_addr_addr_u256`, `eventArgs_positional`, `ExecStmt.emitSingle`; `emitStatic` and
`emitAddrAddrU256` now take `fc.eventsNamed ev = [ei]`), calldata slices `x[lo:hi]` (`sliceObj`;
`sliceObj_bytes`, `sliceObj_bytes_bounds`, `EvalExpr.sliceBytes`; bad bounds revert with empty
data), `bytesN(b)` on a byte array (`explicitConv_bytes_fixedBytes`), `bytesN` indexing
(`fixedBytesIndex_ok/oob`, `EvalExpr.indexFixedBytesNat`).

Changed 2026-10-03: the core relation (`…Core`), the `RD`-based `Dispatch.lean` and the ERC20
core proof are deleted; `Solidity/Equiv.lean` has one relation.  Its `decodingFailed` case accepts
empty revert data, or `Panic(0x41)` when the dispatched function decodes a dynamic argument into
memory (`hasDynamicMemoryParam`, `decodeFailureData`); bridges `Reverted.specDecodingFailed`
(empty) and `Reverted.specDecodingPanic`.

Changed 2026-10-04: a `constant` is converted to its declared type where it is read (rules
`constVar`/`constVarRevert`/`constVarPanic`; `EvalExpr.constVarVal`, `EvalExpr.constVarLitU256`);
a hex literal with 40 digits converts implicitly to `address` (`implicitConv_addrLit`); the
elaborator includes file-level errors, events and constants (after the hierarchy's own).

Changed 2026-10-04 (conformance fixture `Arith`): a number literal that does not fit the other
operand widens the operation to its mobile type (`literalWiden`; `uint8 * 300` is `uint16`
arithmetic); the typed reconstruction of the arguments is part of decoding (`decodeCallArgs`, used
by `decodingFailed`; an out-of-range enum argument is rejected; `decodeCallArgs_none_of_decodeArgs`,
`decodeCallArgs_none_of_ofAbiList`).  An assignment used as a value has the type of its left-hand
side (`assignedValue`, `lvalueTy`; `assignedValue_local`, `assignedValue_storage` and the
`_u256`/`_u256_lit`/`_s256`/`_address` instances; `EvalExpr.assignStorageU256Lit` now yields
`u256Val k`).  An integer array literal takes the common type of all its elements
(`arrayLitIntTy`).  Documented limitation (GUIDE §5, fixture `Cond.sol`): a conditional
`c ? a : b` has the type of the branch taken, not the common type of both branches; the spec states
the conversion.

Changed 2026-10-04 (conformance fixture `Data`): `new T[](n)` and `new bytes(n)` with
`n > 2^64 - 1` revert with `Panic(0x41)` (`allocTooLarge`, rule `newArrayPanic`;
`EvalExpr.newArrayPlain` takes `len < 2 ^ 64`).  An element of a `bytes` state variable is a
`bytes1` location (`bytes1Elem` in `Layout.lean`; it was `uint8`, so reading `blob[i]` had no
derivation).  The DSL parses a tuple assignment whose left side is a parenthesised list
(`(p.x, p.y) = (p.y, p.x);`).

Changed 2026-10-04 (conformance fixture `Flow`): block scoping follows solc when a local hides
another local.  `Frame.hidden` lists the bindings hidden by inner declarations of the same name
(`Frame.bind` records them, `Frame.exitScope` gives them back when the block is left); `return e`
assigns the function's own return variables (`Frame.unwind` in `returnSingle`/`returnMulti`); the
locals of a function body end with the body (`ExecChain.body` yields `exitBlock fr r`), so a second
`_;` of a modifier starts from the parameters and return variables.  Lemmas: `Frame.hidden_setVal`,
`Frame.hidden_bind[_of_none]`, `Frame.mem_bind/_setVal`, `Frame.retVars_bind/_setVal`,
`exitScope_get?` (now needs `fr'.hidden = fr.hidden`), `exitScope_get?'` (general),
`exitScope_get?_shadow`, `exitScope_hidden[_of_eq]`, `Frame.unwind_of_hidden`, `finished_exitBlock`,
`retVals_exitScope`.  Builders: `CallFn.plain` reads the return values from `fr0.exitScope fr2`,
`ExecCtorChain.runPlain/topPlain` thread `immStore (fr2.exitScope fr4)`, the `return*` builders take
`fr1.hidden = []`.  The DSL parses a `for` without initializer (`for (; c; p)`, `for (;;)`).

Changed 2026-10-04 (conformance fixtures `Calls`, `Recv`, `Inherit`, `Libs`): external calls,
low-level calls, `transfer`/`send`, `receive`/`fallback` and inheritance needed no change.  The
elaborator adds the events, errors and constants declared in libraries to `fc.events`, `fc.errors`
and `fc.stateVars`.  A constant's initializer is evaluated without the reader's locals (`constFrame`
in `constVar*`; `EvalExpr.constVarVal`/`constVarLitU256` take the initializer's derivation in
`constFrame fr v.declaredIn` and leave the frame unchanged).

Changed 2026-10-04 (names by scope; fixture `Scopes`).  Every lookup starts from the unit whose code
is running (`fr.here`: a contract of the hierarchy, a library, `""` for a file-level function): its
own declarations and those of its bases, then the file's.
- Lookups (`Elab.lean`): `fc.varIn here x`, `fc.fnsNamedIn here f`, `fc.errorIn here e`,
  `fc.eventsNamedIn here ev`, `fc.modifierIn here name`, `fc.types.structIn/enumIn here n`; the
  qualified forms `fc.varOf q x`, `fc.errorOf`, `fc.eventsOf`, `fc.types.structOf/enumOf`.  They
  replace `var?`, `fnsNamed`, `error?`, `eventsNamed`, `modifier?`, `struct? none`, `enum? none` in
  every rule.  Library functions have entries in `fc.fns` (`fc.unitFns`), so one library function
  can call another by name; library modifiers are in `fc.modifiers` after the hierarchy's.
  `fc.events`/`fc.errors` hold those of every unit (also an interface or a contract outside the
  hierarchy, for `Q.Ev`/`Q.Err`); `fc.usingFor` holds the directives of every unit, each applying
  to code of its unit only (also inside a library).
- Types: a struct or enum is identified by its declaring unit and its name (`StructInfo.qual`; the
  file is `some ""`; `TypeEnv.struct?`/`enum?` match the qualifier exactly).  An enum value carries
  its unit (`Value.enum q ty i`, of type `.user q ty`), so enums with one name in several units stay
  apart in conversions, overloads, `abi.encode` and `using for`.  Types in declarations
  are made canonical by the elaborator, types written in bodies by `TypeEnv.canonTy fr.here` (in
  `declare`, conversions, `new`, `abi.decode`); `canonTy_uint`, …, `TypeEnv.canonTy_user_none`.
- Qualified forms: `Q.CONST` (`qualConst*`, `unitQual`), `Q.E.member` (`qualEnumMember`),
  `Q.S(...)` (`structLitQ*`) and `Q.E(a)` (`convertQ`) for a library, a base or another unit
  (`qualTypeRecv`, `otherUnitRecv`; the library and base call rules take `qualTypeRecv … = false`),
  `revert Q.Err(...)` and `emit Q.Ev(...)` (`errorRef`, `eventsRef`: the `emit`/`revert` rules take
  any callee; `errorRef_ident`, `eventsRef_ident`).
- Constructors follow solc's (legacy) order: initializers base-first, each in the scope of its
  contract (`ExecInits`, `initRoot`); then the arguments of every constructor, the most derived
  contract first, each evaluated with the parameters of the constructor that wrote it
  (`CtorArgsAll`, `CtorArgs`, `ctorFrame`); then the bodies base-first with those arguments
  (`ExecCtorChain tbl`).  Builders: `CtorArgsAll.single`, `ExecCtorChain.runPlain/topPlain`,
  `ExecInits.storageU256`.
- A storage value can be passed to a `memory` parameter of an internal function (`argFits`).
- `elabProgram` rejects two immutables with one name (a private one in a base and one in a derived
  contract): immutables are kept by name (`imm_<name>`).
- Library: hypotheses read `fc.varIn fr.here x = some v` etc.; `FlatContract.fnsNamedIn_vtable/free`,
  `FlatContract.modifierIn_hier`; the modifier builders take `fc.modifierIn fr.here mi.name = some md`;
  `directMember_ident` needs `unitQual … = false` (`unitQual_local/var/noContract`).
- Tests: `Scopes` (clashes at file level, in two libraries and in the contract; three enums with one
  name; `using for` and a modifier inside a library), `PTop`/`QTop`/`RTop` (private names, constructor
  order), `STop` (names through a base, an interface and an unrelated contract).

Changed 2026-10-04 (builtins and conversions; fixture `Builtins`).
- Hashes and chain data: `sha256(b)` / `ripemd160(b)` are STATICCALLs of precompiles 2 / 3
  (`hashCall*`, `hashAddr`, `hashValue`; the success rule asks for 32 bytes of output);
  `blockhash(n)` is the EVM's `BLOCKHASH` (`blockhashValue`), `a.codehash` its `EXTCODEHASH`
  (`memberCodehash`, `codehashValue`); `block.difficulty` equals `block.prevrandao`.
- `bytes.concat` / `string.concat` (`concat*`, `concatKind`, `concatArg`; a type in receiver
  position is resolved without evaluation, `isTypeExprRecv` in `memberCallDirect`).
  `abi.encodeCall(C.f, (args))` (`abiEncodeCall*`, `fnRefDecl`, `encodeCallArgs`).
  `abi.encodeWithSelector` takes any value that converts to `bytes4` (`selectorArg`).  `abi.decode`
  of a value outside its type (an enum out of range) reverts with empty data (`abiDecodeBad`).
- A failed ABI decoding of dynamic data (`abi.decode`, the return data of an external call, the
  returns of a `try`) reverts with `decodeFailData o m tys`: empty data, or `Panic(0x41)` when the
  oracle says the decoder failed at its memory allocation (`Oracle.allocPanic`).  solc's decoder
  allocates a dynamic value before it checks that the value lies inside the data; which check fails
  first depends on the free memory pointer, which the semantics does not model.  The harness takes
  the oracle from the EVM's result (`panicOracle`); scenario `RetUser/decode`.
- Arguments in storage: `keccak256`, `sha256`, `ripemd160` and `concat` read a storage `bytes` /
  `string` (`bytesOf`, `concatParts`); `abi.encode*` copies storage arguments to memory first
  (`abiArgsAbi`).  An inconsistent storage encoding gives `Panic(0x22)` (`keccakPanic`,
  `hashCallPanic`, `concatPanic`, `abiEncodePanic`, `abiEncodeWithSelectorPanic`,
  `abiEncodeWithSignaturePanic`).  `bytes(s)` / `string(b)` on a storage value is the same location
  under the other type; `bytesN(b)` on a storage byte array reads it (`convertStorageBytes*`,
  `storageBytesConv?`; the generic rules `convert*` take `storageBytesConv? … = none`, which
  `EvalExpr.convertPlain` discharges by `rfl`).
- `type(C).name`, `.creationCode`, `.runtimeCode` allocate (`typeMemberBytes`;
  `Config.typeCreationCode` / `typeRuntimeCode`, filled by `setup … creations runtimes`).
  `type(E).min` / `.max` for an enum: `typeMember fc here ty f` takes the running unit.
- Selectors: `E.selector` of an error (4 bytes) or of an event (its topic): `nameSelector`,
  `nameSelectorOf`, `errorEventSelector`; `Q.E.selector` through `selectorMember`.  A function
  reference may go through a variable of contract type (`token.transfer.selector`,
  `abi.encodeCall(token.transfer, …)`: `fnRefContract`, `contractTyName`).  Getters count as
  functions: `fc.contractFns` holds, per unit, one declaration per signature, the most derived one,
  getters included; so `x.v()` on a contract-typed `x` calls a getter and an overridden function is
  found once.
- Conversions: `address` ↔ `bytes20`; `E(i)` for a signed `i` (`Panic(0x21)` outside the range);
  `bytesN(b)` accepts the object behind `bytes(s)`.  `uintN` to `intM` is not an implicit conversion
  (solc rejects it; it made overloads ambiguous).
- Memory: `delete a[i]` / `delete s.f` (`deleteMem*`, `memLValue`).  A memory array records whether
  its static type is `T[n]` (`HeapObj.array e elems fixed`): `abi.encode` encodes it in place.
- Storage: `a.push()` evaluates to the new element (`push0`) and is an lvalue
  (`EvalLValue.pushElem*`: `a.push() = v`, `S storage r = a.push()`); `push` / `pop` on storage
  `bytes` (`pushBytes*`, `popBytes*`, `bytesPush`, `bytesPop`, `pushedByte`).
- DSL: array types in a type tuple (`abi.decode(d, (uint256[], uint8[2]))`); `()` is the empty tuple.
- Library: `EvalExpr.hashMemBytes`, `blockhashU256`, `addressCodehash`, `concatPlain`,
  `abiEncodeCallPlain`, `typeName`, `typeCreationCode`, `typeRuntimeCode`, `errorSelector`,
  `eventSelector`, `pushEmpty` (it now yields the new element), `ExecStmt.deleteMemPlain`;
  `explicitConv_address_bytes20`, `explicitConv_bytes20_address`, `selectorArg_bytes4`;
  `fnRefContract_ident_local/var/noContract/contractVar` (a local or variable of contract type is a
  function reference receiver, so the lemmas ask for `contractTyName … = none`).
- Tests: scenarios `Env`, `Hash`, `AbiC`, `AbiFixed/arrays`, `TypeInfo`, `Conv`, `MemOps` and their
  `/boundaries`, `RetUser/decode`, `StoreStr`.  `Rip/precompile` has cases only where the EVM model's `ripemd160` precompile works:
  it runs a Python script that is found when the harness is started in the `evmlean` package
  directory.  A harness case can set `origin`, `gasPrice` and `blocks`.

## Deferred language features

`mapping(string => …)` / `mapping(bytes => …)` keys (decided 2026-10-03, to do after the branch is
merged): add a `bytes` constructor to `Solm.KeyValue` (`Solm/Syntax/Basic.lean`) rather than
reusing `fixedBytes`.  Then `storageIndex` (`Semantics/Ops.lean`) reads the key bytes from a
literal, a memory/calldata object or a loaded storage string, and `follow` (`Layout.lean`) hashes by
the mapping's declared key type as solc does: `keccak256(h(k) ++ slot)` with `h` = the 32-byte
padded word for value types and the raw bytes for `string`/`bytes`.  No new rules or proof cases;
`keyValueToWord` and the few exhaustive matches on `KeyValue` in Sol⁻ need the new case.

Names, not covered: a state variable written with its contract (`Base.x`, read or assigned); a
modifier invoked with a qualifier (`Base.m`); `using {f, g} for T` (a list of functions) and
file-level `using` directives.

Builtins, not covered: `selfdestruct`; `blobhash` and `block.blobbasefee` (Cancun; the fixtures
are compiled for Shanghai); a function reference whose receiver is neither `this`, a contract name
nor a variable (`IERC20(a).f.selector`); `b.push()` on storage `bytes` used as a value; a storage
`bytes` / `string` passed directly as the message of `require` / `revert`, as the data of
`abi.decode` or of a low-level call (copy it to a memory variable first); user-defined value types
(`type X is uint256`).  `sha256`, `ripemd160` and `ecrecover` are calls of the EVM
model's precompiles: the spec says nothing about the hash values themselves.

## Not covered yet

Solidity side: log-entry instances for event shapes other than the ones listed (the bytes come from
`encodeABIValues?_of_encs` and the per-element lemmas; each `mkLogEntry_*` instance is one `simp`);
arrays of dynamic elements (`string[]`, `bytes[]`) in the ABI;
the `runtimeCodeOf imms = some out` fact of a constructor (per contract).
Shared ABI library: the success lemma for decoding `string`/`bytes` (`EVMReasoning/ABI.lean` has only
the failure cases), needed for `string calldata` parameters through `decodeArgs_eq` and for the
`catch Error(string)` round trip.
EVM side: the `CREATE` and `DELEGATECALL` step lemmas in the trace layer; the solc shapes of
`push`/`pop`, `receive`/`fallback` dispatch, multi-argument custom errors, multi-word encoders and
the string copy routines (no compiled example exhibits them yet).
