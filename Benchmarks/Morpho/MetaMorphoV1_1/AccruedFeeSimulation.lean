import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeRoutines

/-! Matching the final fee guard and fee-calculation paths in an arbitrary loop frame. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure AccruedFeeLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (interest total lost ptr : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  interest : frame.locals.get? "totalInterest" = some (uint256Value interest)
  shares : frame.locals.get? "feeShares" = some (uint256Value ⟨0⟩)
  total : frame.locals.get? "newTotalAssets" = some (uint256Value total)
  lost : frame.locals.get? "newLostAssets" = some (uint256Value lost)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)
  fee : frame.locals.get? "fee" = none

theorem accruedFeeLocals_afterTotals {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {real ptr : UInt256} (last lost : UInt256) (hl : AccruedAssetsTailLocals v frame real ptr) :
    AccruedFeeLocals v (accruedInterestFrame frame last lost real)
      (accruedInterest last lost real) (accruedNewTotal last lost real)
      (accruedNewLost last lost real) ptr := by
  refine ⟨hl.contract, hl.imms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact store_get_self _ _ _
  · dsimp only [accruedInterestFrame, accruedTotalFrame, accruedLossFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
    exact hl.feeShares
  · dsimp only [accruedInterestFrame, accruedTotalFrame]
    rw [store_get_ne _ _ (by decide), store_get_self]
  · dsimp only [accruedInterestFrame, accruedTotalFrame, accruedLossFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · dsimp only [accruedInterestFrame, accruedTotalFrame, accruedLossFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
    exact hl.cursor
  · dsimp only [accruedInterestFrame, accruedTotalFrame, accruedLossFrame]
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
    exact hl.fee

theorem accruedFeeTailReturnSource {frame : Frame} {evm : State}
    {interest fee supply total lost ptr : UInt256} (v : MetaMorphoV1_1Immutables)
    (hl : AccruedFeeLocals v frame interest total lost ptr)
    (hf : evalExpr? config frame evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee))
    (hs : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = supply)
    (hn : interest ≠ ⟨0⟩ ∧ fee ≠ ⟨0⟩)
    (hfit : accruedFeeFits v.DECIMALS_OFFSET interest fee supply total) :
    ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 8)
      (.returned (accruedFeeFinalFrame frame v.DECIMALS_OFFSET interest fee supply total) evm
        [.tuple [uint256Value (accruedFeeShares v.DECIMALS_OFFSET interest fee supply total),
          uint256Value total, uint256Value lost], uint256Value ptr]) := by
  obtain ⟨hc, him, hi, hsh, ht, hlo, hp, hfn⟩ := hl
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc him
  subst c imms
  rw [allocatedAccruedFeeAssetsFunction_fee]
  apply ExecBlock.consNormal (ExecStmt.iteTrue
    (by rw [accruedFeeConditionSource hi hf, decide_eq_true hn])
    (accruedFeeBodySource v locals evm interest fee supply total hi hf ht hsh hs hfit))
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have htotal := (accruedFeeFinalFrame_preserves
    { contract := contract, locals := locals, immutables := immStore v }
    v.DECIMALS_OFFSET interest fee supply total "newTotalAssets"
    (by decide) (by decide) (by decide) (by decide)).trans ht
  have hlost := (accruedFeeFinalFrame_preserves
    { contract := contract, locals := locals, immutables := immStore v }
    v.DECIMALS_OFFSET interest fee supply total "newLostAssets"
    (by decide) (by decide) (by decide) (by decide)).trans hlo
  have hptr := (accruedFeeFinalFrame_preserves
    { contract := contract, locals := locals, immutables := immStore v }
    v.DECIMALS_OFFSET interest fee supply total cursorName
    (by decide) (by decide) (by decide) (by decide)).trans hp
  have hshares : (accruedFeeFinalFrame
      { contract := contract, locals := locals, immutables := immStore v }
      v.DECIMALS_OFFSET interest fee supply total).locals.get? "feeShares" =
      some (uint256Value (accruedFeeShares v.DECIMALS_OFFSET interest fee supply total)) :=
    store_get_self _ _ _
  simp only [evalExprs?, evalExpr?, evalExprList?, htotal, hlost, hptr, hshares,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem accruedFeeTailRevertsSource {frame : Frame} {evm : State}
    {interest fee supply total lost ptr : UInt256} (v : MetaMorphoV1_1Immutables)
    (hl : AccruedFeeLocals v frame interest total lost ptr)
    (hf : evalExpr? config frame evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee))
    (hs : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = supply)
    (hn : interest ≠ ⟨0⟩ ∧ fee ≠ ⟨0⟩)
    (hbad : ¬ accruedFeeFits v.DECIMALS_OFFSET interest fee supply total) :
    ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 8) .reverted := by
  obtain ⟨hc, him, hi, hsh, ht, hlo, hp, hfn⟩ := hl
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc him
  subst c imms
  rw [allocatedAccruedFeeAssetsFunction_fee]
  exact ExecBlock.consRevert (ExecStmt.iteTrue
    (by rw [accruedFeeConditionSource hi hf, decide_eq_true hn])
    (accruedFeeBodyReverts v locals evm interest fee supply total hi hf ht hs hbad))

theorem accruedFeeLocals_feeSource {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap} {interest total lost ptr : UInt256}
    (hl : AccruedFeeLocals v frame interest total lost ptr) (hs : SourceState s0 I σ evm) :
    evalExpr? config frame evm (.storage ⟨"fee", []⟩) =
      .ok (uint256Value (accruedFeeWord I σ)) := by
  have hc := hl.contract
  have hf := hl.fee
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hf
  subst c
  rw [evalStorage_fee evm locals imms hf, hs.storageRead]
  rfl

theorem accruedFeeSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {interest ret lost total ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hl : AccruedFeeLocals v frame interest total lost ptr) (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12353⟩
      ([interest, ret, lost, total, ⟨0⟩] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 8) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (frame' : Frame) (shares : UInt256),
      ExecBlock config frame evm (allocatedAccruedFeeAssetsFunction.body.drop 8)
        (.returned frame' evm
          [.tuple [uint256Value shares, uint256Value total, uint256Value lost], uint256Value ptr]) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        ([lost, total, shares] ++ R) mem aw' rdata σ k' C' := by
  have hf := accruedFeeLocals_feeSource hl hs
  by_cases hn : interest ≠ ⟨0⟩ ∧ accruedFeeWord I σ ≠ ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := accruedFeeGuardFee v (by omega) hn.1 hn.2 rd
    by_cases hfit : accruedFeeFits v.DECIMALS_OFFSET interest (accruedFeeWord I σ)
        (codeOwnerStorageWord I σ ⟨2⟩) total
    · exact .inr ⟨_, _, accruedFeeTailReturnSource v hl hf (hs.storageRead ⟨2⟩) hn hfit,
        accruedFeeReturn v hstack hfit hret h1⟩
    · exact .inl ⟨accruedFeeTailRevertsSource v hl hf (hs.storageRead ⟨2⟩) hn hfit,
        accruedFeeRevert v hstack hfit h1⟩
  · exact .inr ⟨frame, ⟨0⟩,
      accruedFeeNoFeeSource hl.interest hf hl.shares hl.total hl.lost hl.cursor hn,
      accruedFeeGuardNoFee v (by omega) hn hret rd⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
