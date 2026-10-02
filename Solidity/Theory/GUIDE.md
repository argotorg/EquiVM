# Proving a Solidity contract against its bytecode — the recipe

This is the workflow an agent follows to prove `runtimeEquivalenceFor` (and
`constructorEquivalenceFor`) for a contract on the trace stack (`EVMReasoning/Trace.lean`,
`SolcTrace.lean`, `SolcIdioms.lean`) and the Solidity coupling layer (`Solidity/Theory/`).
`STRUCTURE.md` in this directory lists every lemma by file; this file says in which order to use
them.  The usage examples in `Usage.lean` (compiled with the library) show the builders applied to
real statements and to a whole body.

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
- `writeStorageDeep`/`clearStorage` are well-founded: `rw [writeStorageDeep.eq_def]` or
  `rw [clearStorage]` followed by `all_goals first | (simp […]; try rfl) | (intros; simp_all)`.
- Per-contract keccak facts (selectors, mapping slots, event topics) are hypotheses or
  `native_decide`-checked constants, never unfolded.
- Check axioms at the end: `#print axioms` must show only `propext`, `Classical.choice`,
  `Quot.sound`, the `native_decide` auxiliaries and the contract's declared selector facts.

## 4. What the library does not yet give you

See "Not covered yet" in `STRUCTURE.md`.  For those shapes the pattern is: prove the pure fact
about the semantics helper in the contract file (mirroring the nearest `Body.lean` lemma), then a
builder mirroring the nearest `Derivations.lean` one, and move both here once they compile.
