import Benchmarks.Midnight.CollateralValidation
import Benchmarks.Midnight.TouchMarketHeaderSource

/-! Local frames and indexed source values in the collateral-validation loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure CollateralSourceFrame (frame : Frame) (m : MarketData) (i : Nat)
    (previous : AccountAddress) : Prop where
  contract : frame.contract = Benchmarks.Midnight.contract
  market : frame.locals.get? "market" = some (Model.marketValue m.value)
  index : frame.locals.get? "i" = some (.int i)
  previous : frame.locals.get? "previousCollateralToken" = some (.address previous)
  lltvAbsent : frame.locals.get? "isLltvEnabled" = none
  cursorAbsent : frame.locals.get? "isLiquidationCursorEnabled" = none

theorem CollateralSourceFrame.insert {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous)
    (name : Ident) (value : Value)
    (hn : name ∉ ["market", "i", "previousCollateralToken", "isLltvEnabled",
      "isLiquidationCursorEnabled"]) :
    CollateralSourceFrame { frame with locals := frame.locals.insert name value } m i previous := by
  rcases h with ⟨hc, hm, hi, hp, hl, hcu⟩
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem CollateralSourceFrame.setPrevious {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (p : AccountAddress) :
    CollateralSourceFrame
      { frame with locals := frame.locals.insert "previousCollateralToken" (.address p) } m i p := by
  rcases h with ⟨hc, hm, hi, hp, hl, hcu⟩
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem CollateralSourceFrame.setIndex {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (j : Nat) :
    CollateralSourceFrame { frame with locals := frame.locals.insert "i" (.int j) } m j previous := by
  rcases h with ⟨hc, hm, hi, hp, hl, hcu⟩
  constructor <;> simp_all [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

def collateralTokenFrame (frame : Frame) (c : CollateralData) : Frame :=
  { frame with locals := frame.locals.insert "collateralToken" (.address c.token) }

def collateralLltvFrame (frame : Frame) (c : CollateralData) : Frame :=
  wordLocal (collateralTokenFrame frame c) "lltv" c.lltv

def collateralCursorFrame (frame : Frame) (c : CollateralData) : Frame :=
  wordLocal (collateralLltvFrame frame c) "liquidationCursor" c.liquidationCursor

def collateralLifFrame (frame : Frame) (c : CollateralData) : Frame :=
  wordLocal (collateralCursorFrame frame c) "_maxLif" (maxLif c.lltv c.liquidationCursor)

def collateralStepFrame (frame : Frame) (c : CollateralData) : Frame :=
  { (collateralLifFrame frame c) with locals :=
      (collateralLifFrame frame c).locals.insert "previousCollateralToken" (.address c.token) }

theorem collateralTokenFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (c : CollateralData) :
    CollateralSourceFrame (collateralTokenFrame frame c) m i previous :=
  h.insert _ _ (by decide)

theorem collateralLltvFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (c : CollateralData) :
    CollateralSourceFrame (collateralLltvFrame frame c) m i previous :=
  (collateralTokenFrame_inv h c).insert _ _ (by decide)

theorem collateralCursorFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (c : CollateralData) :
    CollateralSourceFrame (collateralCursorFrame frame c) m i previous :=
  (collateralLltvFrame_inv h c).insert _ _ (by decide)

theorem collateralLifFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (c : CollateralData) :
    CollateralSourceFrame (collateralLifFrame frame c) m i previous :=
  (collateralCursorFrame_inv h c).insert _ _ (by decide)

theorem collateralStepFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) (c : CollateralData) :
    CollateralSourceFrame (collateralStepFrame frame c) m i c.token :=
  (collateralLifFrame_inv h c).setPrevious c.token

def collateralAtExpr : Expr := .index (.field (.var "market") "collateralParams") (.var "i")

theorem lookupNth_get {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    lookupNth? xs i = some xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

theorem evalCollateralAt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length) :
    evalExpr? cfg frame evm collateralAtExpr = .ok (Model.collateralValue m.collaterals[i].value) := by
  have hm : evalExpr? cfg frame evm (.field (.var "market") "collateralParams") =
      .ok (.array ((m.collaterals.map CollateralData.value).map Model.collateralValue)) := by
    simp only [evalExpr?, h.market, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  rw [collateralAtExpr, evalExpr?, hm]
  simp only [evalExpr?, h.index, EvalResult.ofOption, bind, pure, EvalResult.bind, evalIndex?]
  rw [if_pos (by simp only [List.length_map, Int.natCast_nonneg, true_and, Int.ofNat_lt]; exact hi)]
  simp only [Int.toNat_natCast]
  rw [lookupNth_get ((m.collaterals.map CollateralData.value).map Model.collateralValue) i
    (by simpa using hi)]
  simp only [List.getElem_map]
  rfl

theorem evalCollateralField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress} {c : CollateralData}
    (h : CollateralSourceFrame frame m i previous) (hi : i < m.collaterals.length)
    (hc : m.collaterals[i] = c) (name : Ident) (value : Value)
    (hv : lookupField? (Model.collateralValue c.value) name = some value) :
    evalExpr? cfg frame evm (.field collateralAtExpr name) = .ok value := by
  rw [evalExpr?, evalCollateralAt h hi, hc]
  simp only [bind, EvalResult.bind, hv, EvalResult.ofOption]
  rfl

end Benchmarks.Midnight
