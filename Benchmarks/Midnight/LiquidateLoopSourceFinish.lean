import Benchmarks.Midnight.LiquidateRecoverySource
import Benchmarks.Midnight.BitmapCallSource

variable {fork : Ethereum.Fork}

/-! The source assignments completing one collateral iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateFinishFrame (frame : Frame) (badDebt recovery bitmap index : UInt256) : Frame :=
  wordLocal (wordLocal (wordLocal (wordLocal frame "__c9" (zeroFloorSubWord badDebt recovery))
    "badDebt" (zeroFloorSubWord badDebt recovery)) "__c10" (bitmapClear bitmap index))
    "_collateralBitmap" (bitmapClear bitmap index)

set_option maxRecDepth 2000000 in
theorem liquidateLoopSourceFinish {frame : Frame} {evm : State}
    {badDebt recovery bitmap index : UInt256}
    (hcontract : frame.contract = contract)
    (hd : frame.locals.get? "badDebt" = some (.int badDebt.toNat))
    (hr : frame.locals.get? "__c8" = some (.int recovery.toNat))
    (hb : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat))
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hindex : index.toNat < 256) :
    ExecBlock fork config frame evm (liquidateLoopBody.drop 11)
      (.ok (liquidateFinishFrame frame badDebt recovery bitmap index) evm) := by
  let f1 := wordLocal frame "__c9" (zeroFloorSubWord badDebt recovery)
  let f2 := wordLocal f1 "badDebt" (zeroFloorSubWord badDebt recovery)
  let f3 := wordLocal f2 "__c10" (bitmapClear bitmap index)
  have ha1 : evalExprs? config frame evm [.var "badDebt", .var "__c8"] =
      .ok [.int badDebt.toNat, .int recovery.toNat] := by
    simp only [evalExprs?, evalWordLocal hd, evalWordLocal hr, pure, bind, EvalResult.bind]
  have hs1 : ExecStmt fork config frame evm (liquidateLoopBody[11]!) (.ok f1 evm) :=
    callZeroFloorSub hcontract ha1
  have hd1 : f1.locals.get? "badDebt" = some (.int badDebt.toNat) := by
    simpa only [f1, wordLocal_get_ne _ _ _ _ (show "__c9" ≠ "badDebt" from by decide)] using hd
  have hs2 : ExecStmt fork config f1 evm (liquidateLoopBody[12]!) (.ok f2 evm) :=
    execLocalAssign hd1 (evalWordLocal (wordLocal_get frame "__c9" _))
  have hb2 : f2.locals.get? "_collateralBitmap" = some (.int bitmap.toNat) := by
    simpa [f2, f1, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hb
  have hi2 : f2.locals.get? "i" = some (.int index.toNat) := by
    simpa [f2, f1, wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hi
  have ha2 : evalExprs? config f2 evm [.var "_collateralBitmap", .var "i"] =
      .ok [.int bitmap.toNat, .int index.toNat] := by
    simp only [evalExprs?, evalWordLocal hb2, evalWordLocal hi2, pure, bind, EvalResult.bind]
  have hs3 : ExecStmt fork config f2 evm (liquidateLoopBody[13]!) (.ok f3 evm) :=
    callBitmapClear hcontract ha2 hindex
  have hb3 : f3.locals.get? "_collateralBitmap" = some (.int bitmap.toNat) := by
    simpa only [f3, wordLocal_get_ne _ _ _ _
      (show "__c10" ≠ "_collateralBitmap" from by decide)] using hb2
  have hs4 : ExecStmt fork config f3 evm (liquidateLoopBody[14]!)
      (.ok (liquidateFinishFrame frame badDebt recovery bitmap index) evm) :=
    execLocalAssign hb3 (evalWordLocal (wordLocal_get f2 "__c10" _))
  exact ExecBlock.consNormal hs1 (ExecBlock.consNormal hs2
    (ExecBlock.consNormal hs3 (ExecBlock.consNormal hs4 (ExecBlock.nil ..))))

end Benchmarks.Midnight
