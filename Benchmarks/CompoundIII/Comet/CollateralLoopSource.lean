import Benchmarks.CompoundIII.Comet.CollateralLoopFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem collateralMembership_exec {v account assets reserved i liquidity frame}
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame) (evm : EVM.State)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8) (hi : i < 256) :
    ExecStmt config frame evm
      (.internalCall "isInAsset" [.var "assetsIn", .var "i", .var "_reserved"] "__c3")
      (.ok (collateralMemberFrame frame (isInAssetBool assets (UInt256.ofNat i) reserved)) evm) := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  exact isInAsset_call frame evm assets (UInt256.ofNat i) reserved _ _ _ "__c3" hf.contract
    ha (by rw [hin]; exact hi) hr
    (by simp only [evalExpr?, hf.assets, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.index, hin, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.reserved, EvalResult.ofOption])

theorem collateralMember_eval (frame : Frame) (evm : EVM.State) (member : Bool) :
    evalExpr? config (collateralMemberFrame frame member) evm (.var "__c3") =
      .ok (.bool member) := by
  simp only [evalExpr?, collateralMemberFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rfl

def CollateralLoopSourceResult (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (result : Option (EVM.State × Bool)) : Prop :=
  match result with
  | none => ExecBlock config frame evm (collateralLoopTail borrow) .reverted
  | some (evm', value) => ∃ final, ExecBlock config frame evm (collateralLoopTail borrow)
      (.returned final evm' (some [.bool value]))

theorem collateralLoop_source_step {frame next : Frame} {evm evm' : EVM.State}
    {borrow : Bool} {result : Option (EVM.State × Bool)}
    (hc : evalExpr? config frame evm assetSearchCond = .ok (.bool true))
    (hb : ExecBlock config frame evm (collateralLoopBody borrow) (.ok next evm'))
    (ht : CollateralLoopSourceResult next evm' borrow result) :
    CollateralLoopSourceResult frame evm borrow result := by
  cases result with
  | none => exact execBlock_while_step hc hb ht
  | some r =>
      obtain ⟨evm'', value⟩ := r
      obtain ⟨final, ht⟩ := ht
      exact ⟨final, execBlock_while_step hc hb ht⟩

theorem collateralLoop_source {v : CometWithExtendedAssetListImmutables}
    {borrow : Bool} {account : AccountAddress} {assets reserved liquidity : UInt256}
    {i : Nat} {evm : EVM.State} {result : Option (EVM.State × Bool)}
    (ht : CollateralLoopTrace v borrow account assets reserved i liquidity evm result)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8) (frame : Frame)
    (hf : CollateralLoopFrame v account assets reserved i liquidity frame) :
    CollateralLoopSourceResult frame evm borrow result := by
  induction ht generalizing frame with
  | exhausted hi =>
      refine ⟨frame, ExecBlock.consNormal (ExecStmt.whileFalse ?_) ?_⟩
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_false (by omega)]
      · exact ABlock.start.returns (collateralResult_eval borrow hf.liquidity)
  | @skipped i liquidity evm result hi hm ht ih =>
      have hi8 : i + 1 < 256 := by have hn := v.numAssets_lt; omega
      have hmcall := collateralMembership_exec hf evm ha hr (by omega)
      rw [hm] at hmcall
      have hfm := hf.member false
      have hinc := assetSearchIncrement_exec (evm := evm) hfm.index hi8
      apply collateralLoop_source_step
        (by rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi])
        (ExecBlock.consNormal hmcall (ExecBlock.consNormal
          (ExecStmt.iteFalse (collateralMember_eval frame evm false) .nil)
          (ExecBlock.consNormal hinc .nil)))
      exact ih _ hfm.next
  | @solvent i liquidity evm hi hm hl =>
      have hi8 : i < 256 := lt_trans hi v.numAssets_lt
      have hmcall := collateralMembership_exec hf evm ha hr hi8
      rw [hm] at hmcall
      have hfm := hf.member true
      refine ⟨collateralMemberFrame frame true,
        ExecBlock.consReturn (ExecStmt.whileReturn ?_ ?_)⟩
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi]
      · apply ExecBlock.consNormal hmcall
        apply ExecBlock.consReturn (ExecStmt.iteTrue (collateralMember_eval frame evm true) ?_)
        apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
        · rw [collateralSolvent_eval hfm.liquidity, decide_eq_true hl]
        · exact ABlock.start.returns (by simp only [evalExpr?, pure])
  | @failed i liquidity evm hi hm hl hv =>
      have hi8 : i < 256 := lt_trans hi v.numAssets_lt
      have hin : (UInt256.ofNat i).toNat = i :=
        UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
      have hmcall := collateralMembership_exec hf evm ha hr hi8
      rw [hm] at hmcall
      have hfm := hf.member true
      have hvalue := collateralValue_source hv (collateralMemberFrame frame true)
        hfm.contract hfm.immutables hfm.storage hfm.account
        (by simp only [evalExpr?, hfm.index, hin, EvalResult.ofOption])
      apply ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi]
      · apply ExecBlock.consNormal hmcall
        apply ExecBlock.consRevert (ExecStmt.iteTrue (collateralMember_eval frame evm true) ?_)
        apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ .nil)
        · exact execBlockAppendReverted hvalue
        · rw [collateralSolvent_eval hfm.liquidity, decide_eq_false (by omega)]
  | @next i liquidity evm evm' d result hi hm hl hv ht ih =>
      have hi8 : i + 1 < 256 := by have hn := v.numAssets_lt; omega
      have hin : (UInt256.ofNat i).toNat = i :=
        UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
      have hmcall := collateralMembership_exec hf evm ha hr (by omega)
      rw [hm] at hmcall
      let f1 := collateralMemberFrame frame true
      have hf1 := hf.member true
      let f2 := collateralValueFrame f1 borrow d
      have hf2 := hf1.value borrow d
      let f3 := collateralAddFrame f2 liquidity (d.value borrow)
      have hf3 := hf2.add (d.value borrow)
      have hvalue := collateralValue_source hv f1 hf1.contract hf1.immutables hf1.storage
        hf1.account (by simp only [f1, evalExpr?, hf1.index, hin, EvalResult.ofOption])
      have hadd := collateralAdd_exec (frame := f2) (evm := evm') hf2.liquidity
        (by simp only [f2, collateralValueFrame, collateralMathFinal,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl) hl hv.value_lt
      have hinc := assetSearchIncrement_exec (evm := evm') hf3.index hi8
      apply collateralLoop_source_step
        (by rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi])
      · apply ExecBlock.consNormal hmcall
        apply ExecBlock.consNormal (ExecStmt.iteTrue (collateralMember_eval frame evm true) ?_)
        · exact ExecBlock.consNormal hinc .nil
        · apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ .nil)
          · exact execBlockAppendOk hvalue (ExecBlock.consNormal hadd .nil)
          · rw [collateralSolvent_eval hf1.liquidity, decide_eq_false (by omega)]
      · exact ih _ hf3.next

end Benchmarks.CompoundIII.Comet
