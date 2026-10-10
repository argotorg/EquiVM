import Benchmarks.UniswapV4PoolManager.TickSqrtWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickSqrtStageStmt (mask factor : UInt256) : Stmt :=
  .ite (.binary .ne
    (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "absTick") (.intLit (Int.ofNat mask.toNat)))
    (.intLit 0))
    [.assign .localVar {base := "price"}
      (.binary (.shr (.uint ⟨256, by decide⟩))
        (.cast (.binary .mul (.var "price") (.intLit (Int.ofNat factor.toNat)))
          (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 128))] []

theorem tickSqrtStageExec {f : Frame} {evm : EVM.State} {absTick price : UInt256}
    (mask factor : UInt256)
    (ha : f.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat)))
    (hp : f.locals.get? "price" = some (.int (Int.ofNat price.toNat))) :
    ∃ f', ExecStmt config f evm (tickSqrtStageStmt mask factor) (.ok f' evm) ∧
      f'.locals.get? "price" = some (.int (Int.ofNat (tickSqrtStage absTick price mask factor).toNat)) ∧
      ∀ name, name ≠ "price" → f'.locals.get? name = f.locals.get? name := by
  have hm : evalExpr? config f evm (.intLit (Int.ofNat mask.toNat)) =
      .ok (.int (Int.ofNat mask.toNat)) := by simp only [evalExpr?, pure]
  have hz : evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have hc := evalNeWords (evalWordAnd (evalLocalValue (cfg := config) (evm := evm) ha) hm) hz
  by_cases hb : UInt256.land absTick mask ≠ ⟨0⟩
  · have hmul := evalWordMul (evalLocalValue (cfg := config) (evm := evm) hp)
      (show evalExpr? config f evm (.intLit (Int.ofNat factor.toNat)) =
        .ok (.int (Int.ofNat factor.toNat)) by simp only [evalExpr?, pure])
    have hs := evalWordShr (b := .intLit 128) (n := 128) (by decide) hmul
      (by simp only [evalExpr?, pure]; rfl)
    let f' : Frame := {f with locals := f.locals.insert "price" (.int
      (Int.ofNat (UInt256.shiftRight (UInt256.mul price factor) (UInt256.ofNat 128)).toNat))}
    refine ⟨f', ExecStmt.iteTrue (by simpa only [decide_eq_true hb] using hc)
      (execBlock_singleton (ExecStmt.assign hs (assignLocalValue hp))), ?_, ?_⟩
    · simpa only [tickSqrtStage, if_pos hb] using store_get_self f.locals "price" _
    · intro name hname
      exact store_get_ne _ _ (beq_eq_false_iff_ne.mpr (Ne.symm hname))
  · refine ⟨f, ExecStmt.iteFalse (by simpa only [decide_eq_false hb] using hc) ExecBlock.nil, ?_, ?_⟩
    · simpa only [tickSqrtStage, if_neg hb] using hp
    · intro name hname; rfl

theorem tickSqrtStagesExec {f : Frame} {evm : EVM.State} {absTick price : UInt256}
    (factors : List (UInt256 × UInt256))
    (ha : f.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat)))
    (hp : f.locals.get? "price" = some (.int (Int.ofNat price.toNat))) :
    ∃ f', ExecBlock config f evm (factors.map fun p => tickSqrtStageStmt p.1 p.2) (.ok f' evm) ∧
      f'.locals.get? "price" = some (.int (Int.ofNat (tickSqrtStages absTick price factors).toNat)) ∧
      ∀ name, name ≠ "price" → f'.locals.get? name = f.locals.get? name := by
  induction factors generalizing f price with
  | nil => exact ⟨f, ExecBlock.nil, hp, fun _ _ => rfl⟩
  | cons pair rest ih =>
    obtain ⟨f1, hs, hp1, hf1⟩ := tickSqrtStageExec pair.1 pair.2 ha hp
    have ha1 := (hf1 "absTick" (by decide)).trans ha
    obtain ⟨f2, hr, hp2, hf2⟩ := ih ha1 hp1
    exact ⟨f2, ExecBlock.consNormal hs hr, hp2,
      fun name hn => (hf2 name hn).trans (hf1 name hn)⟩

end Benchmarks.UniswapV4PoolManager
