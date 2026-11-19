import Benchmarks.Midnight.CollateralValidationSource

/-! The loop condition, increment, and preservation of source locals during validation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def collateralLoopCondition : Expr := .binary .lt (.var "i") marketCollateralLength

def collateralLoopPost : List Stmt :=
  [.assign .localVar { base := "i" }
    (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "i") (.intLit 1)))]

def collateralPostFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (i + 1)) }

def collateralChangedLocals : List Ident :=
  ["i", "previousCollateralToken", "collateralToken", "lltv", "liquidationCursor", "_maxLif"]

def CollateralLocalsPreserved (before after : Frame) : Prop :=
  ∀ name, name ∉ collateralChangedLocals → after.locals.get? name = before.locals.get? name

theorem CollateralLocalsPreserved.refl (frame : Frame) : CollateralLocalsPreserved frame frame :=
  fun _ _ ↦ rfl

theorem CollateralLocalsPreserved.trans {f₀ f₁ f₂ : Frame}
    (h₀ : CollateralLocalsPreserved f₀ f₁) (h₁ : CollateralLocalsPreserved f₁ f₂) :
    CollateralLocalsPreserved f₀ f₂ := fun name hn ↦ (h₁ name hn).trans (h₀ name hn)

theorem collateralInsert_preserved (frame : Frame) (name : Ident) (value : Value)
    (hn : name ∈ collateralChangedLocals) :
    CollateralLocalsPreserved frame { frame with locals := frame.locals.insert name value } := by
  intro other ho
  apply store_get_ne
  apply beq_eq_false_iff_ne.mpr
  intro he
  apply ho
  rw [← he]; exact hn

theorem collateralStepFrame_preserved (frame : Frame) (c : CollateralData) :
    CollateralLocalsPreserved frame (collateralStepFrame frame c) :=
  (collateralInsert_preserved frame "collateralToken" (.address c.token) (by decide)).trans
    ((collateralInsert_preserved _ "lltv" (.int c.lltv.toNat) (by decide)).trans
      ((collateralInsert_preserved _ "liquidationCursor" (.int c.liquidationCursor.toNat) (by decide)).trans
        ((collateralInsert_preserved _ "_maxLif" (.int (maxLif c.lltv c.liquidationCursor).toNat)
          (by decide)).trans
          (collateralInsert_preserved _ "previousCollateralToken" (.address c.token) (by decide)))))

theorem collateralPostFrame_preserved (frame : Frame) (i : Nat) :
    CollateralLocalsPreserved frame (collateralPostFrame frame i) :=
  collateralInsert_preserved frame "i" (.int (i + 1)) (by decide)

theorem evalCollateralLoopCondition {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress}
    (h : CollateralSourceFrame frame m i previous) :
    evalExpr? cfg frame evm collateralLoopCondition = .ok (.bool (decide (i < m.collaterals.length))) := by
  rw [collateralLoopCondition, evalExpr_binary_nonshort (by decide) (by decide)]
  have hi : evalExpr? cfg frame evm (.var "i") = .ok (.int i) := by
    simp only [evalExpr?, h.index, EvalResult.ofOption]
  rw [hi, evalMarketCollateralLength h.market]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_lt]

theorem collateralPostSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {m : MarketData} {i : Nat} {previous : AccountAddress}
    (h : CollateralSourceFrame frame m i previous) (hfit : i + 1 < UInt256.size) :
    ExecBlock cfg frame evm collateralLoopPost (.ok (collateralPostFrame frame i) evm) := by
  apply ExecBlock.consNormal (execLocalAssign h.index ?_) ExecBlock.nil
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  have he := checkedAddSourceOk (cfg := cfg) (stele := frame) (evm := evm)
    (a := UInt256.ofNat i) (b := UInt256.ofNat 1)
    (by simp only [evalExpr?, h.index, EvalResult.ofOption, hin, Int.ofNat_eq_natCast])
    (lhs := .var "i") (rhs := .intLit 1) (by simp only [evalExpr?, pure]; rfl)
    (by simpa only [hin, show (UInt256.ofNat 1).toNat = 1 from rfl] using hfit)
  change evalExpr? cfg frame evm _ = .ok (.int (UInt256.ofNat i + UInt256.ofNat 1).toNat) at he
  rw [uadd_word_ofNat_toNat _ _ (by rw [hin]; exact hfit), hin] at he
  exact he

theorem collateralPostFrame_inv {frame : Frame} {m : MarketData} {i : Nat}
    {previous : AccountAddress} (h : CollateralSourceFrame frame m i previous) :
    CollateralSourceFrame (collateralPostFrame frame i) m (i + 1) previous := h.setIndex (i + 1)

end Benchmarks.Midnight
