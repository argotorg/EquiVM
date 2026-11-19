import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.BitmapSource
import Benchmarks.Midnight.CollateralSourceFrame

/-! Source frames and expression values for the collateral health loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev healthFunction : FunctionDecl := contract.functions[15]!

def healthLoopBody : List Stmt :=
  match healthFunction.body[3]! with
  | .ite _ [_, .while _ body] _ => body
  | _ => []

def healthLoop : Stmt := .while (.binary .ne (.var "_collateralBitmap") (.intLit 0)) healthLoopBody

structure HealthSourceFrame (frame : Frame) (m : MarketData) (id user bitmap maxDebt debt : UInt256) :
    Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  position : frame.locals.get? "_position" = some (.storageRef (positionRef id user) positionType)
  bitmap : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat)
  maxDebt : frame.locals.get? "maxDebt" = some (.int maxDebt.toNat)
  debt : frame.locals.get? "_debt" = some (.int debt.toNat)

theorem HealthSourceFrame.insert {frame : Frame} {m : MarketData}
    {id user bitmap maxDebt debt : UInt256} (h : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (name : Ident) (value : Value)
    (hn : name ∉ ["market", "_position", "_collateralBitmap", "maxDebt", "_debt"]) :
    HealthSourceFrame { frame with locals := frame.locals.insert name value }
      m id user bitmap maxDebt debt := by
  rcases h with ⟨hc, hm, hp, hb, hmax, hd⟩
  simp only [List.mem_cons, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem HealthSourceFrame.setBitmap {frame : Frame} {m : MarketData}
    {id user bitmap maxDebt debt : UInt256} (h : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (b : UInt256) :
    HealthSourceFrame (wordLocal frame "_collateralBitmap" b) m id user b maxDebt debt := by
  rcases h with ⟨hc, hm, hp, hb, hmax, hd⟩
  constructor <;> simp_all [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem HealthSourceFrame.setMaxDebt {frame : Frame} {m : MarketData}
    {id user bitmap maxDebt debt : UInt256} (h : HealthSourceFrame frame m id user bitmap maxDebt debt)
    (d : UInt256) :
    HealthSourceFrame (wordLocal frame "maxDebt" d) m id user bitmap d debt := by
  rcases h with ⟨hc, hm, hp, hb, hmax, hd⟩
  constructor <;> simp_all [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem evalHealthLoopCond {cfg : Config} {frame : Frame} {evm : EVM.State} {bitmap : UInt256}
    (hb : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat)) :
    evalExpr? cfg frame evm (.binary .ne (.var "_collateralBitmap") (.intLit 0)) =
      .ok (.bool (decide (bitmap.toNat ≠ 0))) := by
  simp only [evalExpr?, hb, EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?,
    Reasoning.VyperDispatch.value_int_beq, Int.natCast_eq_zero, decide_not]

theorem healthMsbCall {cfg : Config} {frame : Frame} {evm : EVM.State} {bitmap : UInt256}
    (hc : frame.contract = contract)
    (hb : frame.locals.get? "_collateralBitmap" = some (.int bitmap.toNat)) :
    ExecStmt cfg frame evm (healthLoopBody[0]!)
      (.ok (wordLocal frame "i" (bitmapMsb bitmap)) evm) := by
  let locals : Store := (∅ : Store).insert "bitmap" (.int bitmap.toNat)
  obtain ⟨frame', hf⟩ := bitmapMsbSource (cfg := cfg) (evm := evm)
    (frame := { frame with locals := locals }) (bitmap := bitmap) (by exact store_get_self _ _ _)
  apply internalCallFunctionReturn (callee := bitmapMsbFunction) (locals := locals)
    (calleeStele := frame') (value := some [.int (bitmapMsb bitmap).toNat])
    (argVals := [.int bitmap.toNat])
  · simp only [evalExprs?, evalExpr?, hb, EvalResult.ofOption, bind, pure, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · exact hf

theorem evalHealthCollateralAt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "i" = some (.int index.toNat)) (hbound : index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm collateralAtExpr =
      .ok (Model.collateralValue m.collaterals[index.toNat].value) := by
  have harray : evalExpr? cfg frame evm (.field (.var "market") "collateralParams") =
      .ok (.array ((m.collaterals.map CollateralData.value).map Model.collateralValue)) := by
    simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  rw [collateralAtExpr, evalExpr?, harray]
  simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?]
  rw [if_pos (by simp only [List.length_map, Int.natCast_nonneg, true_and, Int.ofNat_lt]
                 exact hbound)]
  simp only [Int.toNat_natCast]
  rw [lookupNth_get _ index.toNat (by simpa using hbound)]
  simp only [List.getElem_map]
  rfl

theorem evalHealthCollateralAtRevert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {index : UInt256}
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hi : frame.locals.get? "i" = some (.int index.toNat))
    (hbound : ¬ index.toNat < m.collaterals.length) :
    evalExpr? cfg frame evm collateralAtExpr = .revert := by
  have harray : evalExpr? cfg frame evm (.field (.var "market") "collateralParams") =
      .ok (.array ((m.collaterals.map CollateralData.value).map Model.collateralValue)) := by
    simp only [evalExpr?, hm, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  rw [collateralAtExpr, evalExpr?, harray]
  simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, evalIndex?,
    List.length_map, Int.natCast_nonneg, true_and, Int.ofNat_lt, hbound, if_false]

def healthCollateralFrame (frame : Frame) (c : CollateralData) : Frame :=
  { frame with locals := frame.locals.insert "collateralParam" (Model.collateralValue c.value) }

theorem evalHealthOracle {cfg : Config} {frame : Frame} {evm : EVM.State} {c : CollateralData}
    (hc : frame.locals.get? "collateralParam" = some (Model.collateralValue c.value)) :
    evalExpr? cfg frame evm (.field (.var "collateralParam") "oracle") = .ok (.address c.oracle) := by
  simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

theorem evalHealthLltv {cfg : Config} {frame : Frame} {evm : EVM.State} {c : CollateralData}
    (hc : frame.locals.get? "collateralParam" = some (Model.collateralValue c.value)) :
    evalExpr? cfg frame evm (.field (.var "collateralParam") "lltv") = .ok (.int c.lltv.toNat) := by
  simp only [evalExpr?, hc, EvalResult.ofOption, bind, EvalResult.bind]
  rfl

end Benchmarks.Midnight
