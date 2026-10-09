import Benchmarks.CompoundIII.Comet.AbsorbLoopFrame
import Benchmarks.CompoundIII.Comet.AbsorbAssetSource
import Benchmarks.CompoundIII.Comet.InternalValueSource
import Benchmarks.CompoundIII.Comet.CollateralLoopSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem absorbMembership_exec {v absorber account basic old price i delta frame}
    (hf : AbsorbLoopFrame v absorber account basic old price i delta frame) (evm : State)
    (hi : i < 256) :
    ExecStmt config frame evm
      (.internalCall "isInAsset" [.var "assetsIn", .var "i", .var "_reserved"] "__c3")
      (.ok (collateralMemberFrame frame
        (isInAssetBool basic.assets (UInt256.ofNat i) basic.reserved)) evm) := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  exact isInAsset_call frame evm basic.assets (UInt256.ofNat i) basic.reserved _ _ _ "__c3"
    hf.contract basic.assets_lt (by rw [hin]; exact hi) basic.reserved_lt
    (by simp only [evalExpr?, hf.assets, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.index, hin, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.reserved, EvalResult.ofOption])

theorem absorbLoop_source {v : CometWithExtendedAssetListImmutables}
    {absorber account : AccountAddress} {basic : UserBasicData} {old price delta : UInt256}
    {i : Nat} {evm : State} {result : InternalValueOutcome UInt256}
    (ht : AbsorbLoopTrace v account basic.assets basic.reserved i delta evm result)
    (frame : Frame) (hf : AbsorbLoopFrame v absorber account basic old price i delta frame)
    (hib : i ≤ v.numAssets.toNat) :
    internalValueBlockResult config frame evm absorbLoopBlock
      (fun delta frame ↦ AbsorbLoopFrame v absorber account basic old price v.numAssets.toNat delta frame)
      result := by
  induction ht generalizing frame with
  | @exhausted i delta evm hi =>
      have heq : i = v.numAssets.toNat := by omega
      refine ⟨frame, ExecBlock.consNormal (ExecStmt.whileFalse ?_) .nil, ?_⟩
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_false (by omega)]
      · simpa only [heq] using hf
  | @skipped i delta evm result hi hm ht ih =>
      have hi8 : i + 1 < 256 := by have hn := v.numAssets_lt; omega
      have hcall := absorbMembership_exec hf evm (by omega)
      rw [hm] at hcall
      have hfm := hf.member false
      have hinc := assetSearchIncrement_exec (evm := evm) hfm.index hi8
      apply internalValueBlockResult.while_step
        (by rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi])
        (ExecBlock.consNormal hcall (ExecBlock.consNormal
          (ExecStmt.iteFalse (collateralMember_eval frame evm false) .nil)
          (ExecBlock.consNormal hinc .nil)))
      exact ih _ hfm.next (by omega)
  | @reverted i delta evm hi hm ht =>
      have hi8 : i < 256 := lt_trans hi v.numAssets_lt
      have hin : (UInt256.ofNat i).toNat = i :=
        UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
      have hcall := absorbMembership_exec hf evm hi8
      rw [hm] at hcall
      have hfm := hf.member true
      have hasset := absorbAsset_source ht _ absorber hfm.contract hfm.immutables hfm.delta
        hfm.absorber hfm.account hfm.userCollateral hfm.totalsCollateral
        (by simp only [evalExpr?, hfm.index, hin, EvalResult.ofOption])
      apply ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi]
      · exact ExecBlock.consNormal hcall (ExecBlock.consRevert
          (ExecStmt.iteTrue (collateralMember_eval frame evm true) hasset))
  | @staticViolation i delta evm hi hm ht =>
      have hi8 : i < 256 := lt_trans hi v.numAssets_lt
      have hin : (UInt256.ofNat i).toNat = i :=
        UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
      have hcall := absorbMembership_exec hf evm hi8
      rw [hm] at hcall
      have hfm := hf.member true
      have hasset := absorbAsset_source ht _ absorber hfm.contract hfm.immutables hfm.delta
        hfm.absorber hfm.account hfm.userCollateral hfm.totalsCollateral
        (by simp only [evalExpr?, hfm.index, hin, EvalResult.ofOption])
      apply ExecBlock.consStatic (ExecStmt.whileStatic ?_ ?_)
      · rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi]
      · exact ExecBlock.consNormal hcall (ExecBlock.consStatic
          (ExecStmt.iteTrue (collateralMember_eval frame evm true) hasset))
  | @next i delta evm evm' d result hi hm hv ht ih =>
      have hi8 : i + 1 < 256 := by have hn := v.numAssets_lt; omega
      have hin : (UInt256.ofNat i).toNat = i :=
        UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
      have hcall := absorbMembership_exec hf evm (by omega)
      rw [hm] at hcall
      have hfm := hf.member true
      have hasset := absorbAsset_source hv _ absorber hfm.contract hfm.immutables hfm.delta
        hfm.absorber hfm.account hfm.userCollateral hfm.totalsCollateral
        (by simp only [evalExpr?, hfm.index, hin, EvalResult.ofOption])
      have hfa := hfm.asset d
      have hinc := assetSearchIncrement_exec (evm := evm') hfa.index hi8
      apply internalValueBlockResult.while_step
        (by rw [assetSearchCond_eval hf.immutables hf.index, decide_eq_true hi])
        (ExecBlock.consNormal hcall (ExecBlock.consNormal
          (ExecStmt.iteTrue (collateralMember_eval frame evm true) hasset)
          (ExecBlock.consNormal hinc .nil)))
      exact ih _ hfa.next (by omega)

end Benchmarks.CompoundIII.Comet
