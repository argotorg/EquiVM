import Benchmarks.CompoundIII.Comet.TransferCollateralFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem transferCollateralPrefix_source {v src dst asset amount}
    (frame : Frame) (evm : EVM.State) (hf : TransferCollateralArgs frame v src dst asset amount) :
    ExecBlock config frame evm transferCollateralPrefix
      (transferCollateralPrefixResult frame evm src dst asset amount) := by
  let srcBalance := withdrawCollateralBalance evm src asset
  let dstBalance := withdrawCollateralBalance evm dst asset
  let srcNext := transferCollateralSrcNext evm src asset amount
  let dstNext := transferCollateralDstNext evm dst asset amount
  let f1 : Frame := { frame with locals := frame.locals.insert "srcCollateral" (.int srcBalance.toNat) }
  let f2 : Frame := { f1 with locals := f1.locals.insert "dstCollateral" (.int dstBalance.toNat) }
  let f3 : Frame := { f2 with locals := f2.locals.insert "srcCollateralNew" (.int srcNext.toNat) }
  let ready := transferCollateralReadyFrame frame evm src dst asset amount
  have hf1 : TransferCollateralArgs f1 v src dst asset amount :=
    hf.insert "srcCollateral" _ (by decide)
  have hf2 : TransferCollateralArgs f2 v src dst asset amount :=
    hf1.insert "dstCollateral" _ (by decide)
  have hf3 : TransferCollateralArgs f3 v src dst asset amount :=
    hf2.insert "srcCollateralNew" _ (by decide)
  have hready : TransferCollateralArgs ready v src dst asset amount := hf.ready evm
  have hr1 := evalUserCollateral frame evm src asset (.var "src") (.var "asset") false
    hf.contract hf.user (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
  have hr2 := evalUserCollateral f1 evm dst asset (.var "dst") (.var "asset") false
    hf1.contract hf1.user (by simp only [evalExpr?, hf1.dst, EvalResult.ofOption])
    (by simp only [evalExpr?, hf1.asset, EvalResult.ofOption])
  apply ExecBlock.consNormal (ExecStmt.letDecl hr1)
  apply ExecBlock.consNormal (ExecStmt.letDecl hr2)
  have hsrc : evalExpr? config f2 evm (.var "srcCollateral") = .ok (.int srcBalance.toNat) := by
    simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]; rfl
  have ha2 : evalExpr? config f2 evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, hf2.amount, EvalResult.ofOption]
  by_cases hsub : amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat
  · have hsrcNew := checkedNarrowSubSourceOk ⟨128, by decide⟩ hsrc ha2 (low128_lt _) hsub
    apply ExecBlock.consNormal (ExecStmt.letDecl hsrcNew)
    have hdst : evalExpr? config f3 evm (.var "dstCollateral") = .ok (.int dstBalance.toNat) := by
      simp only [evalExpr?, f3, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have ha3 : evalExpr? config f3 evm (.var "amount") = .ok (.int amount.toNat) := by
      simp only [evalExpr?, hf3.amount, EvalResult.ofOption]
    by_cases hadd : (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128
    · have hdstNew := checkedNarrowAddSourceOk ⟨128, by decide⟩ (by decide) hdst ha3 hadd
      apply ExecBlock.consNormal (ExecStmt.letDecl hdstNew)
      have hsval : evalExpr? config ready evm (.var "srcCollateralNew") =
          .ok (.int srcNext.toNat) := by
        simp only [evalExpr?, ready, transferCollateralReadyFrame,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
      have hswrite := assignUserCollateralBalance ready evm src asset
        (.var "src") (.var "asset") srcNext hready.contract hready.user
        (by simp only [evalExpr?, hready.src, EvalResult.ofOption])
        (by simp only [evalExpr?, hready.asset, EvalResult.ofOption])
      cases hp : evm.executionEnv.perm
      · simp only [transferCollateralPrefixResult, transferCollateralPrefixOutcome,
          if_pos hsub, if_pos hadd, hp, Bool.false_eq_true, if_false]
        exact ExecBlock.consStatic (ExecStmt.assignStatic hsval hswrite hp)
      · simp only [transferCollateralPrefixResult, transferCollateralPrefixOutcome,
          if_pos hsub, if_pos hadd, hp, if_true]
        apply ExecBlock.consNormal (ExecStmt.assign hsval hswrite)
        have hdval : evalExpr? config ready
            (storePackedWord evm (userCollateralSlot src asset) srcNext 0 16)
            (.var "dstCollateralNew") = .ok (.int dstNext.toNat) := by
          simp only [evalExpr?, ready, transferCollateralReadyFrame,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
        have hdwrite := assignUserCollateralBalance ready
          (storePackedWord evm (userCollateralSlot src asset) srcNext 0 16) dst asset
          (.var "dst") (.var "asset") dstNext hready.contract hready.user
          (by simp only [evalExpr?, hready.dst, EvalResult.ofOption])
          (by simp only [evalExpr?, hready.asset, EvalResult.ofOption])
        exact ExecBlock.consNormal (ExecStmt.assign hdval hdwrite) .nil
    · simp only [transferCollateralPrefixResult, transferCollateralPrefixOutcome,
        if_pos hsub, if_neg hadd]
      exact ExecBlock.consRevert (ExecStmt.letDeclRevert
        (uintRangeSourceOverflow ⟨128, by decide⟩ (naturalAddSource hdst ha3)
          (by change 2^128 ≤ (withdrawCollateralBalance evm dst asset).toNat + amount.toNat;
              omega)))
  · simp only [transferCollateralPrefixResult, transferCollateralPrefixOutcome, if_neg hsub]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (checkedNarrowSubSourceUnderflow ⟨128, by decide⟩ hsrc ha2
        (by change (withdrawCollateralBalance evm src asset).toNat < amount.toNat; omega)))

end Benchmarks.CompoundIII.Comet
