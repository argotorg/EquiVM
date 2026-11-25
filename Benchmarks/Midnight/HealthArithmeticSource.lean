import Benchmarks.Midnight.HealthSourceFrame

variable {fork : Ethereum.Fork}

/-! Source execution of the arithmetic and bitmap-update part of a health iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def healthProductFrame (frame : Frame) (collateral price lltv : UInt256) : Frame :=
  wordLocal (wordLocal frame "__c2" (healthPriceValue collateral price))
    "__c3" (healthCollateralCapacity collateral price lltv)

def healthStepFrame (frame : Frame) (collateral price lltv bitmap index maxDebt : UInt256) : Frame :=
  wordLocal (wordLocal
    (wordLocal (healthProductFrame frame collateral price lltv) "maxDebt"
      (maxDebt + healthCollateralCapacity collateral price lltv))
    "__c4" (bitmapClear bitmap index)) "_collateralBitmap" (bitmapClear bitmap index)

theorem healthClearCall {cfg : Config} {frame : Frame} {evm : EVM.State} {bitmap index : UInt256}
    (hc : frame.contract = contract)
    (hb : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat))
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hindex : index.toNat < 256) :
    ExecStmt fork cfg frame evm (healthLoopBody[6]!)
      (.ok (wordLocal frame "__c4" (bitmapClear bitmap index)) evm) := by
  let locals : Store := ((∅ : Store).insert "bit" (.int index.toNat)).insert
    "bitmap" (.int bitmap.toNat)
  apply internalCallFunctionReturn (callee := bitmapClearFunction) (locals := locals)
    (argVals := [.int bitmap.toNat, .int index.toNat])
    (value := some [.int (bitmapClear bitmap index).toNat])
  · simp only [evalExprs?, evalExpr?, hb, hi, EvalResult.ofOption, bind, pure, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · exact bitmapClearSource (by exact store_get_self _ _ _)
      (by simp only [locals, store_get_ne _ _ (show ("bitmap" == "bit") = false from rfl),
        store_get_self]) hindex

theorem healthFirstArgs {frame : Frame} {evm : EVM.State} {id user index price : UInt256}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hp : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType))
    (hi : frame.locals.get? "i" = some (.int index.toNat))
    (hprice : frame.locals.get? "price" = some (.int price.toNat)) (hindex : index.toNat < 128) :
    evalExprs? config frame evm
      [healthCollateralExpr, .var "price", .intLit 1000000000000000000000000000000000000] =
      .ok [.int (healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
        (positionSlot id user + ⟨3⟩) index).toNat, .int price.toNat,
        .int (UInt256.ofNat 1000000000000000000000000000000000000).toNat] := by
  simp only [evalExprs?, evalHealthCollateral hc hcanon hp hi hindex, evalExpr?, hprice,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  rfl

theorem healthSecondArgs {cfg : Config} {frame : Frame} {evm : EVM.State}
    {value : UInt256} {c : CollateralData}
    (hv : frame.locals.get? "__c2" = some (.int value.toNat))
    (hc : frame.locals.get? "collateralParam" = some (Model.collateralValue c.value)) :
    evalExprs? cfg frame evm
      [.var "__c2", .field (.var "collateralParam") "lltv", .intLit 1000000000000000000] =
      .ok [.int value.toNat, .int c.lltv.toNat, .int (UInt256.ofNat 1000000000000000000).toNat] := by
  simp only [evalExprs?, evalHealthLltv hc, evalWordLocal hv, evalExpr?,
    EvalResult.bind, bind, pure]
  rfl

set_option maxRecDepth 2000000 in
theorem healthArithmeticSource {frame : Frame} {evm : EVM.State} {m : MarketData}
    {id user bitmap maxDebt debt index price : UInt256} {c : CollateralData}
    (hf : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (hcanon : user.toNat < EVM.addressModulus)
    (hi : frame.locals.get? "i" = some (.int index.toNat))
    (hc : frame.locals.get? "collateralParam" = some (Model.collateralValue c.value))
    (hp : frame.locals.get? "price" = some (.int price.toNat)) (hindex : index.toNat < 128) :
    let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
      (positionSlot id user + ⟨3⟩) index
    (¬ HealthArithmeticSafe collateral price c.lltv maxDebt ∧
      ExecBlock fork config frame evm (healthLoopBody.drop 3) .reverted) ∨
    (HealthArithmeticSafe collateral price c.lltv maxDebt ∧
      ExecBlock fork config frame evm (healthLoopBody.drop 3)
        (.ok (healthStepFrame frame collateral price c.lltv bitmap index maxDebt) evm) ∧
      HealthSourceFrame (healthStepFrame frame collateral price c.lltv bitmap index maxDebt)
        m id user (bitmapClear bitmap index)
        (maxDebt + healthCollateralCapacity collateral price c.lltv) debt) := by
  dsimp only
  let collateral := healthCollateralWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner)
    (positionSlot id user + ⟨3⟩) index
  have ha := healthFirstArgs (evm := evm) hf.contract hcanon hf.position hi hp hindex
  by_cases hmul : collateral.toNat * price.toNat < UInt256.size
  · have hs1 := callMulDivDown (fork := fork) (name := "__c2") hf.contract ha hmul (by decide)
    have hf1 : HealthSourceFrame (wordLocal frame "__c2" (healthPriceValue collateral price))
        m id user bitmap maxDebt debt := hf.insert _ _ (by decide)
    have hc1 : (wordLocal frame "__c2" (healthPriceValue collateral price)).locals.get?
        "collateralParam" = some (Model.collateralValue c.value) := by
      simpa only [wordLocal_get_ne _ _ _ _ (show "__c2" ≠ "collateralParam" from by decide)] using hc
    have ha2 := healthSecondArgs (cfg := config) (evm := evm)
      (wordLocal_get frame "__c2" (healthPriceValue collateral price)) hc1
    by_cases hmul2 : (healthPriceValue collateral price).toNat * c.lltv.toNat < UInt256.size
    · have hs2 := callMulDivDown (fork := fork) (name := "__c3") hf1.contract ha2 hmul2 (by decide)
      have hf2 : HealthSourceFrame (healthProductFrame frame collateral price c.lltv)
          m id user bitmap maxDebt debt := hf1.insert _ _ (by decide)
      by_cases hadd : maxDebt.toNat +
          (healthCollateralCapacity collateral price c.lltv).toNat < UInt256.size
      · have hs3 : ExecStmt fork config (healthProductFrame frame collateral price c.lltv) evm
            (healthLoopBody[5]!) (.ok (wordLocal (healthProductFrame frame collateral price c.lltv)
              "maxDebt" (maxDebt + healthCollateralCapacity collateral price c.lltv)) evm) :=
          execLocalAssign hf2.maxDebt
            (checkedAddSourceOk (evalWordLocal hf2.maxDebt) (evalWordLocal (wordLocal_get ..)) hadd)
        have hf3 := hf2.setMaxDebt (maxDebt + healthCollateralCapacity collateral price c.lltv)
        have hi3 : (wordLocal (healthProductFrame frame collateral price c.lltv) "maxDebt"
            (maxDebt + healthCollateralCapacity collateral price c.lltv)).locals.get? "i" =
            some (.int index.toNat) := by
          simpa only [healthProductFrame,
            wordLocal_get_ne _ _ _ _ (show "maxDebt" ≠ "i" from by decide),
            wordLocal_get_ne _ _ _ _ (show "__c3" ≠ "i" from by decide),
            wordLocal_get_ne _ _ _ _ (show "__c2" ≠ "i" from by decide)] using hi
        have hs4 := healthClearCall (fork := fork) (cfg := config) (evm := evm)
          hf3.contract hf3.bitmap hi3 (by omega)
        have hf4 := hf3.insert "__c4" (.int (bitmapClear bitmap index).toNat) (by decide)
        refine Or.inr ⟨⟨hmul, hmul2, hadd⟩, ?_, hf4.setBitmap (bitmapClear bitmap index)⟩
        refine ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
          (ExecBlock.consNormal hs3 (ExecBlock.consNormal hs4 ?_)))
        exact ExecBlock.consNormal
          (execLocalAssign hf4.bitmap (evalWordLocal (wordLocal_get ..))) ExecBlock.nil
      · refine Or.inl ⟨fun h ↦ hadd h.2.2, ?_⟩
        refine ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2 (ExecBlock.consRevert ?_))
        exact ExecStmt.assignExprRevert
          (checkedAddSourceOverflow (b := healthCollateralCapacity collateral price c.lltv)
            (evalWordLocal hf2.maxDebt)
            (evalWordLocal (wordLocal_get ..)) (by omega))
    · refine Or.inl ⟨fun h ↦ hmul2 h.2.1, ?_⟩
      refine ExecBlock.consNormal hs1 (ExecBlock.consRevert ?_)
      exact callMulDivDownRevert hf1.contract ha2 (fun h ↦ hmul2 h.1)
  · refine Or.inl ⟨fun h ↦ hmul h.1, ExecBlock.consRevert ?_⟩
    exact callMulDivDownRevert hf.contract ha (fun h ↦ hmul h.1)

end Benchmarks.Midnight
