import Benchmarks.UniswapV4PoolManager.PoolModifyValues
import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.CallComposition

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

/-- Locals kept throughout the pool modification, including across internal calls. -/
structure PoolModifyContext (f : Frame) (id : UInt256) (p : PoolModifyParams) : Prop where
  contract : f.contract = Benchmarks.UniswapV4PoolManager.contract
  self : f.locals.get? "self" = some (poolRefValue id)
  params : f.locals.get? "params" = some (poolModifyParamsValue p)
  lower : f.locals.get? "tickLower" = some (.int (EVM.signed p.lower))
  upper : f.locals.get? "tickUpper" = some (.int (EVM.signed p.upper))
  liquidityDelta : f.locals.get? "liquidityDelta" = some (.int p.delta)

theorem PoolModifyContext.insert {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (h : PoolModifyContext f id p) (name : Ident) (value : Value)
    (hn : name ∉ ["self", "params", "tickLower", "tickUpper", "liquidityDelta"]) :
    PoolModifyContext {f with locals := f.locals.insert name value} id p := by
  have hg : ∀ key ∈ ["self", "params", "tickLower", "tickUpper", "liquidityDelta"],
      (f.locals.insert name value).get? key = f.locals.get? key := by
    intro key hk
    apply store_get_ne
    apply beq_eq_false_iff_ne.mpr
    intro he
    exact hn (he ▸ hk)
  exact ⟨h.contract, (hg "self" (by simp)).trans h.self, (hg "params" (by simp)).trans h.params,
    (hg "tickLower" (by simp)).trans h.lower, (hg "tickUpper" (by simp)).trans h.upper,
    (hg "liquidityDelta" (by simp)).trans h.liquidityDelta⟩

theorem PoolModifyContext.resume {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (h : PoolModifyContext f id p) (name : Ident) (values : Option (List Value))
    (hn : name ∉ ["self", "params", "tickLower", "tickUpper", "liquidityDelta"]) :
    PoolModifyContext (resumeAfterInternalCall f name values) id p := h.insert name _ hn

theorem poolTicksValid_bounds {lower upper : UInt256} (h : poolTicksValid lower upper) :
    (EVM.signed lower).natAbs ≤ 887272 ∧ (EVM.signed upper).natAbs ≤ 887272 := by
  rcases h with ⟨hlt, hlo, hup⟩
  omega

end Benchmarks.UniswapV4PoolManager
