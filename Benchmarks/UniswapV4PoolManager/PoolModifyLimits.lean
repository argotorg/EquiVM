import Benchmarks.UniswapV4PoolManager.PoolModifyContext
import Benchmarks.UniswapV4PoolManager.TickSpacingSource
import Benchmarks.UniswapV4PoolManager.ConditionalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyLimitsBlock : List Stmt :=
  [.internalCall "Pool_tickSpacingToMaxLiquidityPerTick" [.field (.var "params") "tickSpacing"] "maxLiquidityPerTick",
   .ite (.binary .gt (.field (.var "state") "liquidityGrossAfterLower") (.var "maxLiquidityPerTick"))
     [.require (.boolLit false)] [],
   .ite (.binary .gt (.field (.var "state") "liquidityGrossAfterUpper") (.var "maxLiquidityPerTick"))
     [.require (.boolLit false)] []]
def poolModifyLimitsStmt : Stmt :=
  .ite (.binary .ge (.var "liquidityDelta") (.intLit 0)) poolModifyLimitsBlock []
def poolModifyLimitsFrame (f : Frame) (spacing : Int) : Frame :=
  {f with locals := f.locals.insert "maxLiquidityPerTick" (.int (tickSpacingLimit spacing))}
def poolModifyLimitsResult (f : Frame) (evm : State) (delta spacing : Int) (gl gu : UInt256) : ExecResult :=
  if 0 ≤ delta then
    if tickSpacingLimit spacing < Int.ofNat gl.toNat ∨ tickSpacingLimit spacing < Int.ofNat gu.toNat then .reverted
    else .ok (poolModifyLimitsFrame f spacing) evm
  else .ok f evm

theorem poolModifyLimitsResult_frame {f f' : Frame} {evm post : State} {delta spacing : Int} {gl gu : UInt256}
    (h : poolModifyLimitsResult f evm delta spacing gl gu = .ok f' post) :
    f' = (if 0 ≤ delta then poolModifyLimitsFrame f spacing else f) ∧ post = evm := by
  unfold poolModifyLimitsResult at h
  split_ifs at h <;> cases h <;> simp_all only [if_pos, if_false, and_self]

theorem poolModifyLimitsResult_context {f f' : Frame} {evm post : State} {id : UInt256}
    {p : PoolModifyParams} {delta spacing : Int} {gl gu : UInt256}
    (hc : PoolModifyContext f id p)
    (h : poolModifyLimitsResult f evm delta spacing gl gu = .ok f' post) : PoolModifyContext f' id p := by
  rw [(poolModifyLimitsResult_frame h).1]
  split_ifs
  · exact hc.insert "maxLiquidityPerTick" _ (by decide)
  · exact hc

theorem poolModifyLimitsResult_get {f f' : Frame} {evm post : State} {delta spacing : Int} {gl gu : UInt256}
    (h : poolModifyLimitsResult f evm delta spacing gl gu = .ok f' post)
    (name : Ident) (hn : ("maxLiquidityPerTick" == name) = false) :
    f'.locals.get? name = f.locals.get? name := by
  rw [(poolModifyLimitsResult_frame h).1]
  split_ifs
  · exact store_get_ne _ _ hn
  · rfl

theorem poolModifyLimitsChecks {f : Frame} {evm : State} {fl fu : Bool} {gl gu : UInt256} {limit : Int}
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu))
    (hm : f.locals.get? "maxLiquidityPerTick" = some (.int limit)) :
    ExecBlock config f evm (poolModifyLimitsBlock.drop 1)
      (if limit < Int.ofNat gl.toNat ∨ limit < Int.ofNat gu.toNat then .reverted else .ok f evm) := by
  have hl : evalExpr? config f evm
      (.binary .gt (.field (.var "state") "liquidityGrossAfterLower") (.var "maxLiquidityPerTick")) =
      .ok (.bool (decide (limit < Int.ofNat gl.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide),
      evalStructField (evalLocalValue hs) rfl, evalLocalValue hm]
    rfl
  have hu : evalExpr? config f evm
      (.binary .gt (.field (.var "state") "liquidityGrossAfterUpper") (.var "maxLiquidityPerTick")) =
      .ok (.bool (decide (limit < Int.ofNat gu.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide),
      evalStructField (evalLocalValue hs) rfl, evalLocalValue hm]
    rfl
  have hsl := execStmt_rejectIf hl
  have hsu := execStmt_rejectIf hu
  by_cases hlo : limit < Int.ofNat gl.toNat
  · rw [if_pos (Or.inl hlo)]
    exact ExecBlock.consRevert (by simpa only [decide_eq_true hlo, if_true] using hsl)
  · by_cases hup : limit < Int.ofNat gu.toNat
    · rw [if_pos (Or.inr hup)]
      exact ExecBlock.consNormal (by simpa only [decide_eq_false hlo, Bool.false_eq_true, if_false] using hsl)
        (ExecBlock.consRevert (by simpa only [decide_eq_true hup, if_true] using hsu))
    · rw [if_neg (by tauto)]
      exact ExecBlock.consNormal (by simpa only [decide_eq_false hlo, Bool.false_eq_true, if_false] using hsl)
        (execBlock_singleton (by simpa only [decide_eq_false hup, Bool.false_eq_true, if_false] using hsu))

theorem poolModifyLimits {f : Frame} {evm : State} {p : PoolModifyParams} {fl fu : Bool} {gl gu : UInt256}
    (hf : f.contract = contract)
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p))
    (hd : f.locals.get? "liquidityDelta" = some (.int p.delta))
    (hs : f.locals.get? "state" = some (poolModifyStateValue fl gl fu gu)) :
    ExecStmt config f evm poolModifyLimitsStmt
      (poolModifyLimitsResult f evm p.delta (EVM.signed p.spacing) gl gu) := by
  have hc : evalExpr? config f evm (.binary .ge (.var "liquidityDelta") (.intLit 0)) =
      .ok (.bool (decide (0 ≤ p.delta))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hd]
    simp only [evalExpr?, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hdelta : 0 ≤ p.delta
  · rw [poolModifyLimitsResult, if_pos hdelta]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true hdelta] using hc)
    have hcall := tickSpacingCall (f := f) (evm := evm) hf
      (evalStructField (evalLocalValue hp) (field := "tickSpacing") rfl) "maxLiquidityPerTick"
    have htail := poolModifyLimitsChecks (f := poolModifyLimitsFrame f (EVM.signed p.spacing)) (evm := evm)
      ((store_get_ne _ _ (by decide : ("maxLiquidityPerTick" == "state") = false)).trans hs)
      (store_get_self _ _ _)
    by_cases hbad : tickSpacingLimit (EVM.signed p.spacing) < Int.ofNat gl.toNat ∨
        tickSpacingLimit (EVM.signed p.spacing) < Int.ofNat gu.toNat
    · rw [if_pos hbad] at htail ⊢
      exact ExecBlock.consNormal hcall htail
    · rw [if_neg hbad] at htail ⊢
      exact ExecBlock.consNormal hcall htail
  · rw [poolModifyLimitsResult, if_neg hdelta]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hdelta] using hc) ExecBlock.nil

end Benchmarks.UniswapV4PoolManager
