import Benchmarks.UniswapV4PoolManager.PoolModifyTicks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyTickAfterFrame_get (f : Frame) (evm : State) (id : UInt256) (tick delta : Int)
    (upper fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) (name : Ident)
    (hs : ("state" == name) = false) (ha : (poolModifyTickAlias upper == name) = false)
    (hr : (poolModifyTickRet upper == name) = false) :
    (poolModifyTickAfterFrame f evm id tick delta upper fl gl fu gu).locals.get? name = f.locals.get? name :=
  (poolModifyTickFrame_get _ _ _ _ _ _ _ _ name hs).trans (store_get_ne2 _ _ _ ha hr)

theorem poolModifyTwoTicksResult_get {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyTwoTicksResult f evm id p = .ok f' post) (name : Ident)
    (hs : ("state" == name) = false) (ha : ∀ upper, (poolModifyTickAlias upper == name) = false)
    (hr : ∀ upper, (poolModifyTickRet upper == name) = false) : f'.locals.get? name = f.locals.get? name := by
  rw [(poolModifyTwoTicksResult_normal h).1]
  exact (poolModifyTickAfterFrame_get _ _ _ _ _ true _ _ _ _ name hs (ha true) (hr true)).trans
    (poolModifyTickAfterFrame_get _ _ _ _ _ false _ _ _ _ name hs (ha false) (hr false))

theorem poolModifyTicksResult_get {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyTicksResult f evm id p = .ok f' post) (name : Ident)
    (hn : name = "delta" ∨ name = "feeDelta") : f'.locals.get? name = f.locals.get? name := by
  unfold poolModifyTicksResult at h
  split_ifs at h
  · obtain ⟨f1, mid, hlo, hup⟩ := continueBlockResult_ok h
    apply (poolModifyTickFinishResult_get hup name (by rcases hn with rfl | rfl <;> decide)
      (by intro upper; cases upper <;> rcases hn with rfl | rfl <;> decide)
      (by intro upper; cases upper <;> rcases hn with rfl | rfl <;> decide)).trans
    exact poolModifyTwoTicksResult_get hlo name (by rcases hn with rfl | rfl <;> decide)
      (by intro upper; cases upper <;> rcases hn with rfl | rfl <;> decide)
      (by intro upper; cases upper <;> rcases hn with rfl | rfl <;> decide)
  · cases h
    rfl

def poolModifyTicksFlipped (evm : State) (id : UInt256) (p : PoolModifyParams) (upper : Bool) : Bool :=
  if p.delta ≠ 0 then tickFlipped (if upper then poolModifyUpperPacked evm id p else poolModifyLowerPacked evm id p) p.delta
  else false

theorem poolModifyTicksResult_flips {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (hs : f.locals.get? "state" = some (poolModifyStateValue false ⟨0⟩ false ⟨0⟩))
    (h : poolModifyTicksResult f evm id p = .ok f' post) :
    ∃ gl gu, f'.locals.get? "state" = some
      (poolModifyStateValue (poolModifyTicksFlipped evm id p false) gl (poolModifyTicksFlipped evm id p true) gu) := by
  have hv := poolModifyTicksResult_state hs h
  by_cases hd : p.delta ≠ 0
  · refine ⟨EVM.wordOfInt (tickGrossAfterInt (poolModifyLowerPacked evm id p) p.delta),
      EVM.wordOfInt (tickGrossAfterInt (poolModifyUpperPacked evm id p) p.delta), ?_⟩
    simpa only [poolModifyTicksState, poolModifyTicksFlipped, if_pos hd, poolModifyTwoTicksState,
      Bool.false_eq_true, if_false, if_true] using hv
  · exact ⟨⟨0⟩, ⟨0⟩, by simpa only [poolModifyTicksState, poolModifyTicksFlipped, if_neg hd] using hv⟩

end Benchmarks.UniswapV4PoolManager
