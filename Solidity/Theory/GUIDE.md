# Proving a Solidity contract against its bytecode — the recipe

This is the workflow an agent follows to prove `runtimeEquivalenceFor` (and
`constructorEquivalenceFor`) for a contract on the trace stack (`EVMReasoning/Trace.lean`,
`SolcTrace.lean`, `SolcIdioms.lean`) and the Solidity coupling layer (`Solidity/Theory/`).
`STRUCTURE.md` in this directory lists every lemma by file; this file says in which order to use
them.  The usage examples in `Usage.lean` (compiled with the library) show the builders applied to
real statements and to a whole body.  `Solidity/Examples/ERC20/` is a complete proof following this
recipe (six functions, constructor, dispatcher, capstone `erc20Correct`).

## 0. Inputs of a contract proof

| Input | Where it comes from | Form |
|---|---|---|
| Spec | `solidity% …` program, `elabProgram program target` | `fc : FlatContract`, `cfg : Config` (layout hooks) |
| Runtime bytecode | `solc` output, pinned in `Bytecode.lean` | `code : ByteArray` with `@[valid_jumps]` |
| Selectors | keccak of the canonical signatures | per-contract facts `selectorOf sig = …` (keccak is not evaluable in the elaborator: state them once, check with the harness) |
| Storage layout | the spec's layout hooks | facts `cfg.storage.layout er evm = some (uint256Loc slot)` (or `boolOffset0Loc`, `addressOffset0Loc`, `bytes32Loc`, a packed `{ slot, offset, size, … }`) for every reference the body touches |
| Mapping slots | keccak of `key ++ slot` | facts `solcSlotWord …` ↔ `keyRef …` (per contract) |

Never derive these by unfolding: `decodeArgs_eq`, `readScalar_of_loc`, `writeScalar_of_loc` and
the builders consume them as hypotheses.

## 1. One function, one case: the three derivations

Every case (success, each revert path) of every entry point is one theorem with three parts.

### 1a. The EVM run

Start from `initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I` and thread a `Run` through:

1. Prologue and guards: `Run.solcGuardPrologue`, `Run.solcGuardCallvalueZero` (or
   `…NonzeroRevert` for the non-payable revert), `Run.solcCalldataOk` / `…ShortRevert`.
2. Selector: `Run.solcSelectorLoad`, then the dispatcher arms `Run.selectorArm*Auto` /
   `Run.dispatchTo` down to the function body pc (`Run.solcDispatchReachBody` for the common shape).
3. Argument decoding: `Run.solc*External*` decoders (address masks, length checks).
4. Body: opcode by opcode with `evm_run h with [op, …]`, `Run.sload`/`Run.sstore`, the memory
   `*Var` forms for symbolic offsets, and the `SolcIdioms` shapes (checked add, panic tails, array
   guards, loops via `Run.countingLoop`/`Run.whileLoop`, custom errors, return block).
5. Terminal: `Returned code s0 w out` (`Run.solcReturnBlock`, `retVar`) or `Reverted code s0 d`
   (`Run.solcPanicTail`, `Run.solcErrorStringRevertTail`, `Run.solcCustomErrorRevert[U256]`,
   `Run.solcRevertBlock`).

Keep the world `w` explicit: every `SSTORE` gives
`{ w with accounts := sstoreAccountMap … }`, every `LOG` a `w.logs.push …`, every `CALL` the
callee's `Θ` result.

### 1b. The spec derivation

Build `solidityExec … (.returned m vs) conv` (or `(.reverted d)`) with `solidityExec.call` /
`callReverted` / `nonPayable` / `receive*` / `fallback*`:

- dispatch facts: `selectorDispatch_of_size`, `decodeArgs_eq` + the `EVMReasoning/ABI.lean`
  decode lemma for the parameter shape, `payableOrNoValue_of_zero`, `ofAbi_*`;
- the body: `CallFn.plain` (binds parameters and zeroes return slots), then an
  `ExecBlock.cons` chain of statement builders (`ExecStmt.requireTrue`, `subAssignU256`,
  `assignStorageU256[Lit]`, `varDeclU256[Lit]`, `iteTrue/iteFalse`, `emitStatic`, `returnU256`,
  `revertErrorNoArgs`, …), each fed by expression builders (`EvalExpr.localVal`,
  `mappingAddrU256`, `mappingIndexScalar`, `storageFieldU256`, `addU256[Lit]`, `ltU256Lit`,
  `keccakPacked`, `convertPlain`, …).  Frame lookups are discharged by `frame_simp`.
  The return values are read after the body's own locals are dropped: `hrets` of `CallFn.plain`
  is stated on `fr0.exitScope fr2` (close it with `retVals_exitScope`), and the `return*`
  builders take `fr1.hidden = []` (`by simp` on the frame).
- reverts: the builder of the failing statement gives `(.reverted d)` with the exact bytes
  (`errorStringData`, `panicData 0x11`, `selectorOf sig ++ …`), and `ExecBlock.consRevert`
  propagates it.

`Usage.lean` builds single statements this way (arithmetic with literals, keccak of
`abi.encodePacked`, mapping writes, custom errors, `unchecked`, `delete`, `emit`) and the whole
SimpleAuction `bid()` body.

### 1c. Coupling and the bridge

`WorldEquiv w m` (accounts equal up to `accountMapEquiv`, same created set, same log series) holds
at entry by `WorldEquiv.init` and is transported step by step:

| EVM step | Spec step | Lemma |
|---|---|---|
| `SSTORE slot val` | `storeU256 m slot val` | `WorldEquiv.sstore` |
| `SLOAD slot` | `loadU256 m slot` | `WorldEquiv.sload` (gives the word equality) |
| `LOGn` | `m.pushLog le` | `WorldEquiv.pushLog` + `mkLogEntry_static` |
| `CALL` (value 0 / with value) | `callViaEVM` | `WorldEquiv.callMade` / `callMadeValue` / `callNotMade*` |

Close the case with `Returned.specExecutionW o hcode h hspec hw henc` (`henc` by the ABI return
encoding lemma of the return shape) or `Reverted.specRevert o hcode h hspec`.  Dispatch-level
reverts have their own bridges: `Reverted.specNonPayable`, `specNoDispatch`,
`specDecodingFailed`, `specFallbackNonPayable`, `specUndispatched`.  Constructors use
`Returned.specCtorW` / `Reverted.specCtorRevert` with `solidityCtorExec` and `ExecCtorChain.*`.

## 2. Assembling the contract theorem

Case-split on the selector bytes (`I.calldata.extract 0 4`) and `I.calldata.size`, then inside
each function on the conditions that choose the path (balance checks, overflow bounds, custom-error
guards).  The EVM side of the dispatcher is shared (`Run.dispatchNoMatch`,
`Run.solcDispatch{NonPayable,Short,NoMatch}Revert`).  Combine the cases into the ∀-closed
`runtimeEquivalence*` statements of `Solidity/Equiv.lean` and `Behaviors.lean`.

## 3. Rules that save hours

- Read `STRUCTURE.md` → "Reduction footgun" and "Usage idioms" before writing any tactic proof.
  Never `simp [binop, …]`, `dsimp`, `rfl` or `decide` on `settle`/`inRange`/`IntTy.max` with a
  numeral operand; rewrite with the `_of_unify`/`settle_*`/`*_lit` lemmas.
- Builders take the `Local` explicitly when a hypothesis mentions it; the machine of
  `EvalExpr.local`/`EvalLValue.local` is passed as `(m := m)`.
- Right operands are evaluated first (`EvalExpr.binary`): the `hb` hypothesis of a binary builder
  runs in the incoming frame, `ha` after it.
- Inside `theorem ExecPost.*` write `Option.some`; a bare `some` resolves to `ExecPost.some`.
- Scopes: a frame records in `hidden` the bindings that inner declarations of the same name hide.
  Without shadowing it stays as it was (`Frame.hidden_bind_of_none` for a fresh declaration,
  `Frame.hidden_setVal`), and a lookup after a block is `exitScope_get?` (side condition
  `fr'.hidden = fr.hidden`, by `simp`).  With one shadowing declaration use `exitScope_get?_shadow`.
  State the freshness of a block-local (`fr.get? "t" = none`) as a hypothesis when the frame is
  abstract.
- `writeStorageDeep`/`clearStorage` are well-founded: `rw [writeStorageDeep.eq_def]` or
  `rw [clearStorage]` followed by `all_goals first | (simp […]; try rfl) | (intros; simp_all)`.
- Per-contract keccak facts (selectors, mapping slots, event topics) are hypotheses or
  `native_decide`-checked constants, never unfolded.
- Check axioms at the end: `#print axioms` must show only `propext`, `Classical.choice`,
  `Quot.sound`, the `native_decide` auxiliaries and the contract's declared selector facts.
- Read the disassembly of every tail you reuse a shape for: solc emits the same `Error(string)`
  tail once with `PUSH2 … JUMP` into the shared revert block and once falling straight into it
  (ERC20 `transferFrom`), and the address mask `AND` with either operand order (`u256_land_comm`).
- Give builders their expected type when the frame is not fixed by an argument
  (`have h : EvalExpr … := EvalExpr.subU256 …`); otherwise the `by frame_simp` discharges see
  metavariables.  `ExecCtorChain.topPlain` needs `(step := ⟨…⟩)` explicitly.
- After `rw [h_size]` a goal `a + b ≤ n` on numerals is often closed by `rw`'s `rfl`; a following
  `omega` then fails with "no goals".
- Creation code: `I.code = creation ++ args`.  Import `EVMReasoning.Initcode` and discharge decodes
  with `decode_append_left_window` and jump destinations with `D_J_contains_append_left`
  (ERC20 `Constructor.lean`: `ctor_decode`, `ctor_jd`, `ctor_run`).  The argument copy
  `CODECOPY` lands past the end of memory (`write_gap_eq`); the hash and free-pointer lemmas for a
  memory larger than 96 bytes are the `twoWordHashMem_*_of_le` family.

## 4. What the library does not yet give you

See "Not covered yet" in `STRUCTURE.md`.  For those shapes the pattern is: prove the pure fact
about the semantics helper in the contract file (mirroring the nearest `Body.lean` lemma), then a
builder mirroring the nearest `Derivations.lean` one, and move both here once they compile.

## 5. Transcribing the source: one rule about types

The spec language has no static type system; a value carries its type at run time, and that is the
type solc gives the expression everywhere except in one construct.  A conditional `c ? a : b` has
in solc the common type of both branches, in the spec the type of the branch taken.  When the two
branches have different types (or are both number literals) and the conditional is an operand of
another operator or an argument of `abi.encodePacked`, write the conversion in the spec, as solc
inserts it: `(c ? uint256(a) : b) + 1`.  Nothing false can be proved if this is forgotten: the
spec then disagrees with the bytecode and the proof fails there.  The fixture
`Solidity/Test/Fixtures/Cond.sol` pins the deviation.

## 6. Transcribing the source: names

Names are resolved as in Solidity: from the contract or library whose code is running, then its
bases, then the file.  The same name may be declared in several units (`Tick.Info` and
`Position.Info`, a `WAD` in a library and in the contract), and a library function may call another
function of its library by name.  Write the source as it is, including the qualified forms
`Q.CONST`, `Q.Struct(...)`, `Q.Enum.member`, `Q.Enum(x)`, `revert Q.Err(...)`, `emit Q.Ev(...)` and
`Q.f(...)`, with `Q` a library or a base (for types, errors and events also an interface or any
other contract).  `using L for T;` and `using {f, L.g} for T;` are available in a contract, a
library and the file (`global` included), also for a contract or interface type (`using SafeERC20
for IERC20; token.safeTransfer(…)`).  Not available: `Base.x` for a state variable.  In proofs,
the lookup facts mention the running unit: `fc.varIn fr.here "x" = some v`, with `fr.here` the
contract that declares the function.

## 7. Transcribing the source: builtins

The global functions and members of Solidity 0.8 are available as written: `keccak256`, `sha256`,
`ripemd160`, `ecrecover`, `blockhash`, `addmod`, `mulmod`, `gasleft`, the `block`, `tx` and `msg`
members, `a.balance`, `a.code`, `a.codehash`, `abi.encode`, `abi.encodePacked`,
`abi.encodeWithSelector`, `abi.encodeWithSignature`, `abi.encodeCall`, `abi.decode`,
`bytes.concat`, `string.concat`, `type(T).min` / `.max`, `type(I).interfaceId`, `type(C).name`,
`type(C).creationCode`, `type(C).runtimeCode`, and `.selector` of a function, an error or an event.
- `type(C).creationCode` and `type(C).runtimeCode` read `Config.typeCreationCode` /
  `typeRuntimeCode`: give `setup` the bytecode tables (`creations`, `runtimes`).
- A function reference (`f.selector`, `abi.encodeCall(f, …)`) is `this.f`, `C.f` or `x.f` with `x` a
  variable of contract type; write `IERC20 t = IERC20(a); t.f.selector` for `IERC20(a).f.selector`.
- `sha256`, `ripemd160` and `ecrecover` are calls of the precompiles: a proof gets the call as a
  hypothesis (`EvalExpr.hashMemBytes`, `EvalExpr.ecrecoverPlain`), not a hash value.
- A decode of dynamic data that fails (`abi.decode`, return data) reverts with empty data or with
  `Panic(0x41)`, as the oracle says (`Oracle.allocPanic`, `decodeFailData`): pick the oracle that
  matches the bytecode's decoder for the input at hand.
- Not available: `selfdestruct`, `blobhash`, `block.blobbasefee`.

## 8. Calldata parameters

A `calldata` array or struct parameter is decoded without validating its words; a word is
validated when an element or field is read, or when the object is ABI-encoded (a bad word reverts
with empty data), and an array of value-type words copied to memory is cleaned, not validated (an
enum out of range in such a copy is `Panic(0x21)` when the element is used).
One whose elements or fields are dynamically encoded (`bytes[]`, `T[][]`, a struct with a `bytes`
field) stays in the calldata (`Value.cdRef`): an element's offset and length are checked when the
element is used, as solc does.  In proofs the arguments of an encoding (`abiEncodePlain`,
`keccakPacked`, …) come with `hraw : ∀ v ∈ vs, hasRaw … = false`, discharged by
`simp [fuelDefault]` for scalar arguments; a calldata array argument needs the preparation step
(`prepareArgs`) spelled out.  The dispatcher prepares a function's returned values the same way
(`solidityExec.call`), so a `calldata`-typed return (`returns (uint16[] calldata)`) with a bad
word reverts with empty data.

## 9. Transcribing the source: user-defined value types

`type T is U;` is available in the file, a contract, a library and an interface, with `T.wrap`,
`T.unwrap` and the qualified forms `Q.T`, `Q.T.wrap(…)`.  A value of the type is
`Value.wrapped q T v` with `v` the value of the underlying type; storage, the ABI and mapping keys
use the underlying type, so the slot and encoding lemmas of the underlying type apply
(`readScalar_valueType`, `writeScalar_wrapped`, `scalarToAbi_wrapped`, `abiTypeOf_valueType`).
Builders: `EvalExpr.wrapPlain`, `EvalExpr.unwrapPlain` with `valueTypeRecv_ident` /
`valueTypeRecv_qual` for the receiver.

One rule: an operator bound with `using {f as +} for T global` is written as the call it stands
for, and the binding is left out of the directive (the DSL rejects `as +`).  `a + b` on values of
`T` becomes `f(a, b)`, `-a` becomes `g(a)`.  solc evaluates the operator as that call, left operand
first, so the call is exact (see "User-defined operators" in `STRUCTURE.md`).
