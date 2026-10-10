import Benchmarks.UniswapV4PoolManager.PoolModifyTickSource
import Benchmarks.UniswapV4PoolManager.PoolModifyContext

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyTickAfterFrame (f : Frame) (evm : State) (id : UInt256) (tick delta : Int)
    (upper fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) : Frame :=
  let packed := tickFieldWord evm id tick .liquidityPacked
  let flipped := tickFlipped packed delta
  let gross := EVM.wordOfInt (tickGrossAfterInt packed delta)
  poolModifyTickFrame
    (resumeAfterInternalCall (poolModifyTickAliasFrame f id upper) (poolModifyTickRet upper)
      (some [.bool flipped, .int (Int.ofNat gross.toNat)])) upper flipped gross fl gl fu gu

theorem poolModifyTickResult_normal {f f' : Frame} {evm post : State} {id : UInt256} {tick delta : Int}
    {upper fl fu : Bool} {gl gu : UInt256}
    (h : poolModifyTickResult f evm id tick delta upper fl gl fu gu = .ok f' post) :
    f' = poolModifyTickAfterFrame f evm id tick delta upper fl gl fu gu ∧
    post = poolUpdateTickPost evm id tick delta upper := by
  unfold poolModifyTickResult at h
  dsimp only at h
  generalize hr : poolUpdateTickResult (poolModifyTickAliasFrame f id upper) evm id tick delta upper = r at h
  cases r with
  | returned cf post values =>
    cases h
    have hv := poolUpdateTickReturnedValues hr
    exact ⟨by rw [hv]; rfl, poolUpdateTickReturnedState hr⟩
  | ok | reverted | «break» | «continue» | staticViolation => cases h

theorem poolModifyTickAfterFrame_context {f : Frame} {p : PoolModifyParams} {id : UInt256}
    (h : PoolModifyContext f id p) (evm : State) (tick delta : Int)
    (upper fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) :
    PoolModifyContext (poolModifyTickAfterFrame f evm id tick delta upper fl gl fu gu) id p := by
  exact (((h.insert (poolModifyTickAlias upper) _ (by cases upper <;> decide)).resume
    (poolModifyTickRet upper) _ (by cases upper <;> decide)).insert "state" _ (by decide)).insert "state" _ (by decide)

theorem poolModifyTickFrame_get (f : Frame) (upper flipped : Bool) (gross : UInt256)
    (fl : Bool) (gl : UInt256) (fu : Bool) (gu : UInt256) (name : Ident)
    (hn : ("state" == name) = false) :
    (poolModifyTickFrame f upper flipped gross fl gl fu gu).locals.get? name = f.locals.get? name := by
  simp only [poolModifyTickFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hn, Bool.false_eq_true, if_false]

theorem poolModifyTickResult_frame {f f' : Frame} {evm post : State} {id : UInt256} {tick delta : Int}
    {upper fl fu : Bool} {gl gu : UInt256}
    (h : poolModifyTickResult f evm id tick delta upper fl gl fu gu = .ok f' post) :
    ∃ values, f' = poolModifyTickFrame
      (resumeAfterInternalCall (poolModifyTickAliasFrame f id upper) (poolModifyTickRet upper) values) upper
      (tickFlipped (tickFieldWord evm id tick .liquidityPacked) delta)
      (EVM.wordOfInt (tickGrossAfterInt (tickFieldWord evm id tick .liquidityPacked) delta)) fl gl fu gu := by
  exact ⟨_, (poolModifyTickResult_normal h).1⟩

end Benchmarks.UniswapV4PoolManager
