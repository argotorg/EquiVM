import Benchmarks.CompoundIII.Comet.WithdrawCollateralModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

structure WithdrawCollateralFrame (frame : Frame) (src asset : AccountAddress)
    (amount : UInt256) : Prop where
  contract : frame.contract = contract
  src : frame.locals.get? "src" = some (.address src)
  asset : frame.locals.get? "asset" = some (.address asset)
  amount : frame.locals.get? "amount" = some (.int amount.toNat)
  user : frame.locals.get? "userCollateral" = none
  totals : frame.locals.get? "totalsCollateral" = none

theorem WithdrawCollateralFrame.read {frame src asset amount}
    (hf : WithdrawCollateralFrame frame src asset amount) (balance : UInt256) :
    WithdrawCollateralFrame (withdrawCollateralReadFrame frame balance) src asset amount := by
  refine ⟨hf.contract, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hf.src
  · simpa only [withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hf.asset
  · simpa only [withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hf.amount
  · simpa only [withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hf.user
  · simpa only [withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hf.totals

theorem WithdrawCollateralFrame.ready {frame src asset amount}
    (hf : WithdrawCollateralFrame frame src asset amount) (balance : UInt256) :
    WithdrawCollateralFrame (withdrawCollateralReadyFrame frame balance amount)
      src asset amount := by
  have hr := hf.read balance
  refine ⟨hr.contract, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr.src
  · simpa only [withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr.asset
  · simpa only [withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr.amount
  · simpa only [withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr.user
  · simpa only [withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using hr.totals

theorem withdrawCollateralPrefix_source (frame : Frame) (evm : EVM.State)
    (src asset : AccountAddress) (amount : UInt256)
    (hf : WithdrawCollateralFrame frame src asset amount) :
    ExecBlock config frame evm withdrawCollateralPrefix
      (withdrawCollateralPrefixResult frame evm src asset amount) := by
  let balance := withdrawCollateralBalance evm src asset
  let total := withdrawCollateralTotal evm asset
  let f1 := withdrawCollateralReadFrame frame balance
  let f2 := withdrawCollateralReadyFrame frame balance amount
  have hf1 := hf.read balance
  have hf2 := hf.ready balance
  have hread : evalExpr? config frame evm withdrawCollateralBalanceExpr =
      .ok (.int balance.toNat) := evalUserCollateral frame evm src asset
    (.var "src") (.var "asset") false hf.contract hf.user
    (by simp only [evalExpr?, hf.src, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
  have hb : evalExpr? config f1 evm (.var "srcCollateral") = .ok (.int balance.toNat) := by
    simp only [evalExpr?, f1, withdrawCollateralReadFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hamt : evalExpr? config f1 evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, f1, hf1.amount, EvalResult.ofOption]
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  by_cases hbnd : amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat
  · have hsub := checkedNarrowSubSourceOk ⟨128, by decide⟩ hb hamt (low128_lt _) hbnd
    apply ExecBlock.consNormal (ExecStmt.letDecl hsub)
    have htotal : evalExpr? config f2 evm (.storage withdrawCollateralTotalRef) =
        .ok (.int total.toNat) := by
      simpa only [← hf2.contract] using evalTotalsCollateralFieldVar evm f2.locals
        f2.immutables asset false "asset" hf2.totals hf2.asset
    have hamt2 : evalExpr? config f2 evm (.var "amount") = .ok (.int amount.toNat) := by
      simp only [evalExpr?, f2, hf2.amount, EvalResult.ofOption]
    by_cases htnd : amount.toNat ≤ (withdrawCollateralTotal evm asset).toNat
    · have htsub := checkedNarrowSubSourceOk ⟨128, by decide⟩ htotal hamt2 (low128_lt _) htnd
      have htwrite := assignTotalsCollateralBalance f2 evm asset (.var "asset")
        (UInt256.sub total amount) hf2.contract hf2.totals
        (by simp only [evalExpr?, f2, hf2.asset, EvalResult.ofOption])
      cases hp : evm.executionEnv.perm
      · simp only [withdrawCollateralPrefixResult, withdrawCollateralPrefixOutcome,
          if_pos hbnd, if_pos htnd, hp, Bool.false_eq_true, if_false]
        exact ExecBlock.consStatic (ExecStmt.assignStatic htsub htwrite hp)
      · simp only [withdrawCollateralPrefixResult, withdrawCollateralPrefixOutcome,
          if_pos hbnd, if_pos htnd, hp, if_true]
        apply ExecBlock.consNormal (ExecStmt.assign htsub htwrite)
        have he : evalExpr? config f2
            (storePackedWord evm (totalsCollateralSlot asset) (UInt256.sub total amount) 0 16)
            (.var "srcCollateralNew") = .ok (.int (UInt256.sub balance amount).toNat) := by
          simp only [evalExpr?, f2, withdrawCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
        have hw := assignUserCollateralBalance f2
          (storePackedWord evm (totalsCollateralSlot asset) (UInt256.sub total amount) 0 16)
          src asset (.var "src") (.var "asset")
          (UInt256.sub balance amount) hf2.contract hf2.user
          (by simp only [evalExpr?, f2, hf2.src, EvalResult.ofOption])
          (by simp only [evalExpr?, f2, hf2.asset, EvalResult.ofOption])
        exact ExecBlock.consNormal (ExecStmt.assign he hw) .nil
    · simp only [withdrawCollateralPrefixResult, withdrawCollateralPrefixOutcome,
        if_pos hbnd, if_neg htnd]
      exact ExecBlock.consRevert (ExecStmt.assignExprRevert
        (checkedNarrowSubSourceUnderflow ⟨128, by decide⟩ htotal hamt2 (by
          change (withdrawCollateralTotal evm asset).toNat < amount.toNat; omega)))
  · simp only [withdrawCollateralPrefixResult, withdrawCollateralPrefixOutcome, if_neg hbnd]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert
      (checkedNarrowSubSourceUnderflow ⟨128, by decide⟩ hb hamt (by
        change (withdrawCollateralBalance evm src asset).toNat < amount.toNat; omega)))

end Benchmarks.CompoundIII.Comet
