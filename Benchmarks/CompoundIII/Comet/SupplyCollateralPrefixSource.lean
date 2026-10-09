import Benchmarks.CompoundIII.Comet.SupplyCollateralFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem supplyCollateralPrefix_source {sender dst asset amount out}
    (frame : Frame) (evm : EVM.State)
    (hf : SupplyCollateralArgs frame sender dst asset amount out) :
    ExecBlock config frame evm supplyCollateralPrefix
      (supplyCollateralPrefixResult frame evm dst asset amount out) := by
  let total := withdrawCollateralTotal evm asset
  let reserved := supplyCollateralReserved evm asset
  let balance := withdrawCollateralBalance evm dst asset
  let next := supplyCollateralNext evm dst asset amount
  let read := { frame with locals := frame.locals.insert "totals" (totalsCollateralValue total reserved) }
  let totals := supplyCollateralTotalsFrame frame evm asset amount
  let bal := { totals with locals := totals.locals.insert "dstCollateral" (.int balance.toNat) }
  let ready := supplyCollateralReadyFrame frame evm dst asset amount
  have hrargs : SupplyCollateralArgs read sender dst asset amount out :=
    hf.insert "totals" (totalsCollateralValue total reserved) (by decide)
  have htargs : SupplyCollateralArgs totals sender dst asset amount out := hf.totalsFrame evm
  have hbargs : SupplyCollateralArgs bal sender dst asset amount out :=
    htargs.insert "dstCollateral" (.int balance.toNat) (by decide)
  have hfargs : SupplyCollateralArgs ready sender dst asset amount out := hf.ready evm
  have hread := evalTotalsCollateral frame evm asset (.var "asset") hf.contract hf.totals
    (by simp only [evalExpr?, hf.asset, EvalResult.ofOption])
  have hrt : read.locals.get? "totals" = some (totalsCollateralValue total reserved) := by
    simp only [read, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
  have htotal := evalTotalsCollateralTotal (show evalExpr? config read evm (.var "totals") =
    .ok (totalsCollateralValue total reserved) by simp only [evalExpr?, hrt, EvalResult.ofOption])
  have hra : evalExpr? config read evm (.var "amount") = .ok (.int amount.toNat) := by
    simp only [evalExpr?, hrargs.amount, EvalResult.ofOption]
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  by_cases ht : (withdrawCollateralTotal evm asset).toNat + amount.toNat < 2^128
  · have hadd := checkedNarrowAddSourceOk ⟨128, by decide⟩ (by decide) htotal hra ht
    have hw := assignLocalCollateralTotal (cfg := config) (evm := evm) (total + amount) hrt
    apply ExecBlock.consNormal (ExecStmt.assign hadd hw)
    have hget : totals.locals.get? "totals" =
        some (totalsCollateralValue (total + amount) reserved) := by
      simp only [totals, supplyCollateralTotalsFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert]; rfl
    have heq : evalExpr? config totals evm supplyCollateralCapExpr =
        .ok (.bool (decide ((supplyCollateralTotalNext evm asset amount).toNat ≤
          (calldataWord out 224).toNat))) := by
      simp only [supplyCollateralCapExpr, evalExpr?, hget, htargs.info, EvalResult.ofOption,
        bind, EvalResult.bind, totalsCollateralValue, assetValue, lookupField?, lookupAssoc,
        evalBinaryOp?]
      change EvalResult.ok (Value.bool
        (decide ((↑(total + amount).toNat : Int) ≤ ↑(calldataWord out 224).toNat))) = _
      simp only [Int.ofNat_le]
      rfl
    by_cases hcap : (supplyCollateralTotalNext evm asset amount).toNat ≤
        (calldataWord out 224).toNat
    · apply ExecBlock.consNormal (ExecStmt.requireTrue (heq.trans (by rw [decide_eq_true hcap])))
      have hbalance := evalUserCollateral totals evm dst asset (.var "dst") (.var "asset") false
        htargs.contract htargs.user
        (by simp only [evalExpr?, htargs.dst, EvalResult.ofOption])
        (by simp only [evalExpr?, htargs.asset, EvalResult.ofOption])
      apply ExecBlock.consNormal (ExecStmt.letDecl hbalance)
      have hbl : evalExpr? config bal evm (.var "dstCollateral") = .ok (.int balance.toNat) := by
        simp only [evalExpr?, bal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]; rfl
      have hba : evalExpr? config bal evm (.var "amount") = .ok (.int amount.toNat) := by
        simp only [evalExpr?, hbargs.amount, EvalResult.ofOption]
      by_cases hb : (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128
      · have hsum := checkedNarrowAddSourceOk ⟨128, by decide⟩ (by decide) hbl hba hb
        apply ExecBlock.consNormal (ExecStmt.letDecl hsum)
        have hval : ∀ evm', evalExpr? config ready evm' (.var "totals") =
            .ok (totalsCollateralValue (total + amount) reserved) := by
          intro evm'
          simp only [evalExpr?, ready, supplyCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
            Std.HashMap.getElem?_insert]
          change EvalResult.ofOption .unboundVariable (totals.locals.get? "totals") = _
          rw [hget]; rfl
        have hwrite := assignTotalsCollateral ready evm asset (.var "asset")
          (total + amount) reserved hfargs.contract hfargs.totals
          (by simp only [evalExpr?, hfargs.asset, EvalResult.ofOption])
        cases hp : evm.executionEnv.perm
        · simp only [supplyCollateralPrefixResult, supplyCollateralPrefixOutcome,
            if_pos ht, if_pos hcap, if_pos hb, hp, Bool.false_eq_true, if_false]
          exact ExecBlock.consStatic (ExecStmt.assignStatic (hval evm) hwrite hp)
        · simp only [supplyCollateralPrefixResult, supplyCollateralPrefixOutcome,
            if_pos ht, if_pos hcap, if_pos hb, hp, if_true]
          apply ExecBlock.consNormal (ExecStmt.assign (hval evm) hwrite)
          have hnext : evalExpr? config ready
              (storeTotalsCollateral evm asset (total + amount) reserved)
              (.var "dstCollateralNew") = .ok (.int next.toNat) := by
            simp only [evalExpr?, ready, supplyCollateralReadyFrame, Std.HashMap.get?_eq_getElem?,
              Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
          have hwrite2 := assignUserCollateralBalance ready
            (storeTotalsCollateral evm asset (total + amount) reserved) dst asset
            (.var "dst") (.var "asset") next hfargs.contract hfargs.user
            (by simp only [evalExpr?, hfargs.dst, EvalResult.ofOption])
            (by simp only [evalExpr?, hfargs.asset, EvalResult.ofOption])
          exact ExecBlock.consNormal (ExecStmt.assign hnext hwrite2) .nil
      · simp only [supplyCollateralPrefixResult, supplyCollateralPrefixOutcome,
          if_pos ht, if_pos hcap, if_neg hb]
        exact ExecBlock.consRevert (ExecStmt.letDeclRevert
          (uintRangeSourceOverflow ⟨128, by decide⟩ (naturalAddSource hbl hba)
            (by change 2^128 ≤ (withdrawCollateralBalance evm dst asset).toNat + amount.toNat;
                omega)))
    · simp only [supplyCollateralPrefixResult, supplyCollateralPrefixOutcome,
        if_pos ht, if_neg hcap]
      exact ExecBlock.consRevert (ExecStmt.requireFalse (heq.trans (by rw [decide_eq_false hcap])))
  · simp only [supplyCollateralPrefixResult, supplyCollateralPrefixOutcome, if_neg ht]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (uintRangeSourceOverflow ⟨128, by decide⟩ (naturalAddSource htotal hra)
        (by change 2^128 ≤ (withdrawCollateralTotal evm asset).toNat + amount.toNat; omega)))

end Benchmarks.CompoundIII.Comet
