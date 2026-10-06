# Brief: port to the strong runtime relation

## Task

Restate and re-prove the runtime theorem of each contract below with
`runtimeEquivalenceAnyPerm` instead of `runtimeEquivalence`. The strong relation has no
`I.perm = true` precondition, so it also covers calls entered with STATICCALL.

Contracts (proved ones only; the `Benchmarks/Scaffolds` stubs are out of scope):

- `Benchmarks/Auction`, `Benchmarks/WETH9`
- `Benchmarks/Dss/`: Dai, Jug, Vat, Pot, Spot, Vow, LinearDecrease,
  StairstepExponentialDecrease, ExponentialDecrease, Cat, Clipper, Cure, Dog, End, Flapper,
  Flipper, Flopper, GemJoin, DaiJoin

Add the source's events to every benchmark spec (see "Adding events" below). Do not change
constructor proofs: constructor equivalence keeps `I.perm = true` (init code never runs
in static mode).

## Step 0: baseline

Build each target on the commit before the static-mode change and record which already fail.
Report pre-existing failures instead of repairing them silently.

## What changed in the shared code

- `Solm/Semantics/Exec.lean`: new result `ExecResult.staticViolation` and `*Static` rules
  (`assignStatic`, `deleteStatic`, `pushValStatic`, `pushGrowStatic`, `popStatic`, `newStatic`,
  `emitStatic`, `internalCallStatic`, `externalCallStatic`, `lowLevelCallStatic`,
  `checkedCallStatic`, `whileStatic`, `forInitStatic`, `ExecForLoop.bodyStatic` /
  `iteratePostStatic` / `continuePostStatic`, `ExecBlock.consStatic`,
  `ExecFuncBody.execBlockStatic`). Exhaustive `cases` on these derivations need new arms.
- `Solm/Syntax/Basic.lean`: new statement `Stmt.emit`. Exhaustive matches on `Stmt` need an arm.
- `Solm/Semantics/Calls.lean`: the callee permission passed to `Θ` is now
  `perm && evm.executionEnv.perm`. Proofs that rewrote the flag to `true` must handle
  `true && I.perm` (`Bool.true_and`). `typedCallViaEVM_callMade_sameInputs` uses
  `(callPerm && evm.executionEnv.perm)`. Known affected sites, all with `callPerm := I.perm`:
  Dss/Cat (`BiteBody`, `BiteBodyReach`, `BiteBodyKick`, `BiteTrace`) and Dss/Pot (`Join`,
  `Exit`).
- `Solm/Equiv.lean`: `execResultsEquiv.staticHalt` pairs EVM `StaticModeViolation` with Solm
  `.staticViolation`. The weak relations are unchanged. New: `runtimeEquivalenceAnyPerm`,
  `runtimeEquivalenceWithWFAnyPerm`, `contractEquivalence{,WF,With,WithWF}AnyPerm`, each with
  `.toPerm`.
- `Reasoning/Reach.lean`: `RDstatic`; static steps `RD.sstoreStatic`, `RD.log0Static` …
  `RD.log4Static`, `RD.callValueStatic`; `permSplit_true`, `permSplit_false`, `permSplit_bind`,
  `staticOr_bind`; `RDstatic.reEquivStaticHalt`, `RDstatic.reEquivReceiveStaticHalt`;
  loop rule `RD.execForLoopOrRevertOrStaticCarryFull`; value-CALL lemmas
  `RD.callValue{Made,InsufficientBalance,DepthLimit}{,EmptyInOut}Or` that take
  `ee.perm = true ∨ value = ⟨0⟩`.
- `Reasoning/Solc.lean`: the seven combinators that contain an SSTORE or LOG3 have `…Split`
  versions without `hperm` (`RD.solcSingleMappingStoreDebitMemSplit`,
  `RD.solcSingleMappingStoreCreditMemSplit`, `RD.solcNestedMappingStoreOuterSstoreSplit`,
  `RD.solcNestedMappingCallerStoreMemSplit`, `RD.solcLockEnterOkSplit`,
  `RD.solcMaskedTransferLog3AndJumpSplit`, `RD.solcPlainLog3AndJumpSplit`).

## Adding events

In each benchmark's `SpecSyntax.lean`, add the `event` declarations and every `emit` statement of
the Solidity source, at the same place as in the source. Logs are still not compared. The events
matter in static mode: the bytecode aborts at its first event or storage write, and the spec must
then abort too, which it does only at a state-changing statement. Without the `emit`, a path where
the source emits and then reverts or returns without a storage write cannot be proved.

Proof side, following `Examples/ERC20`:

- Every Solm derivation that passes an `emit` needs a step for it. Use `ABlock.emitStep`, or
  `ExecStmt.emit` directly, with a lemma that evaluates the event's arguments (ERC20:
  `evalExprs_transfer_event` in `Transfer.lean`).
- If the `emit` is the first state change on a path, the static body ends with
  `ExecBlock.consStatic (ExecStmt.emitStatic heval hperm)`, and the EVM side uses `RD.log*Static`.
- Arguments that can revert use `ExecStmt.emitArgsRevert`.

## Recipe

1. For every path, find the first state-changing opcode in the bytecode: SSTORE, LOG0–LOG4,
   CALL with nonzero value, CREATE/CREATE2, SELFDESTRUCT, TSTORE. Check the order in the
   bytecode, not the source. Example: `BlindAuction.auctionEnd` runs LOG1 before its first
   SSTORE.
2. The EVM segment holding that opcode drops `hperm` and concludes
   `(I.perm = true ∧ P) ∨ (I.perm = false ∧ RDstatic code g s0)`:

   ```lean
   by_cases hperm : I.perm = true
   swap
   · exact Or.inr ⟨by simpa using hperm, rdX.sstoreStatic (by simpa using hperm) hdec hov⟩
   refine Or.inl ⟨hperm, ?_⟩
   -- the old proof, unchanged
   ```

   Callers on paths where that segment is not the first write use
   `permSplit_true hperm (segment …)`. To continue after a split, use
   `refine permSplit_bind (segment …) fun hperm h => ?_`. A loop that may run zero iterations
   concludes `P ∨ (I.perm = false ∧ RDstatic …)`; a later unconditional write closes it with
   `staticOr_bind`.
3. The Solm static body is the success derivation cut at the first write, closed with its
   `*Static` rule, e.g. `ExecBlock.consStatic (ExecStmt.assignStatic heval hassign hperm)`.
   Inside a branch: `ExecBlock.consStatic (ExecStmt.iteTrue hcond (ExecBlock.consStatic …))`.
   Internal call: `ExecStmt.internalCallStatic` with a static callee body.
4. In the body lemma, remove `(hperm : I.perm = true)` and add `by_cases hperm : I.perm = true`
   where the path is committed to its first write. The false side is
   `(permSplit_false hpf segment).reEquivStaticHalt hcode hd hdec hbodyStatic`.
5. A value-carrying CALL that can run under `I.perm = false` with value zero: use the `…Or`
   CALL lemmas with `Or.inr hzero`. With nonzero value both sides halt: `RD.callValueStatic`
   and `ExecStmt.lowLevelCallStatic` (or `externalCallStatic`, `checkedCallStatic`).
6. Remove unused `hperm` binders and arguments (`hsize hperm` becomes `hsize`). Capstone:

   ```lean
   theorem xxxCorrect : runtimeEquivalenceAnyPerm config xxxBytecode contract := by
     refine runtimeEquivalenceAnyPerm.intro ?_
     intro σ σ₀ g A I hcode hsize
   ```

   Bundle: `contractEquivalenceAnyPerm.intro` (or the `WF` / `With` / `WithWF` variant the
   contract already uses).

## Worked examples in this repository

- `Examples/ERC20/Transfer.lean`: single first write, split segment and static body.
- `Examples/StringStoreLite`: loops that may run zero iterations (`staticOr_bind`), residual
  lemmas that return a split.
- `Examples/BlindAuction/Reveal`: loop whose body writes only on some iterations
  (`RevealLoopBodyOutcome` has a static case, `RD.execForLoopOrRevertOrStaticCarryFull`);
  post-loop CALL whose value is zero or not (`Reveal/PostLoop.lean`).
- `Examples/OpenZeppelinBench/ERC6909/TransferFrom`: several branches with different first
  writes.
- `Examples/Ballot/Delegate*.lean`: continuation-style frontier; branch at the leaf.
- `Examples/UniswapV2Pair/Correct.lean`: large proof left unchanged; each state-changing function
  gets `uniswapXBodyAnyPerm`, which uses the old body proof when `I.perm = true` and a separate
  static case otherwise.

## Acceptance

- `lake build <Contract>.Correct` succeeds.
- The capstone states `runtimeEquivalenceAnyPerm` (or `runtimeEquivalenceWithWFAnyPerm`).
- `#print axioms` shows the same footprint as before: `propext`, `Classical.choice`,
  `Quot.sound` and documented `native_decide` facts; no `sorryAx`, no new axioms.
- Do not change `Solm/`, `EVM/`, `ABI/` or existing `Reasoning/` statements without asking.
  Report any case that looks unprovable before working around it.
