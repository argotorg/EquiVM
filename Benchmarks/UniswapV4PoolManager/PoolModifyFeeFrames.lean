import Benchmarks.UniswapV4PoolManager.PoolModifyFees

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyFeeDeltaWord (evm : State) (id : UInt256) (p : PoolModifyParams) : UInt256 :=
  balanceDeltaWord (poolModifyPositionOwed evm id p false) (poolModifyPositionOwed evm id p true)
def poolModifyFeesFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : Frame :=
  let f1 := poolModifyPositionAfterFrame (poolModifyFeesPreludeFrame f evm id p) evm id (poolModifyPositionKey p) p.delta
    (poolModifyFeeWord evm id p false) (poolModifyFeeWord evm id p true)
  poolModifyFeeDeltaFrame f1 (poolModifyPositionOwed evm id p false) (poolModifyPositionOwed evm id p true)

theorem poolModifyFeesResult_normal {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyFeesResult f evm id p = .ok f' post) :
    f' = poolModifyFeesFrame f evm id p ∧ post = positionUpdatePost evm id (poolModifyPositionKey p) p.delta
      (poolModifyFeeWord evm id p false) (poolModifyFeeWord evm id p true) := by
  obtain ⟨f1, mid, hpos, hfee⟩ := continueBlockResult_ok h
  obtain ⟨rfl, hmid⟩ := poolModifyPositionUpdateResult_normal hpos
  obtain ⟨rfl, rfl⟩ := poolModifyFeeDeltaResult_normal hfee
  exact ⟨rfl, hmid⟩

theorem poolModifyFeesResult_context {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (h : poolModifyFeesResult f evm id p = .ok f' post) : PoolModifyContext f' id p := by
  rw [(poolModifyFeesResult_normal h).1]
  exact poolModifyFeeDeltaFrame_context
    (poolModifyPositionAfterFrame_context (poolModifyFeesPreludeFrame_context hc evm) _ _ _ _) _ _

theorem poolModifyFeesResult_fee {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyFeesResult f evm id p = .ok f' post) :
    f'.locals.get? "feeDelta" = some (.int (EVM.signed (poolModifyFeeDeltaWord evm id p))) := by
  rw [(poolModifyFeesResult_normal h).1]
  exact store_get_self _ _ _

theorem poolModifyFeesResult_get {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyFeesResult f evm id p = .ok f' post) (name : Ident) (hn : name = "delta" ∨ name = "state") :
    f'.locals.get? name = f.locals.get? name := by
  rw [(poolModifyFeesResult_normal h).1]
  apply (poolModifyFeeDeltaFrame_get _ _ _ name
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)).trans
  apply (poolModifyPositionAfterFrame_get _ _ _ _ _ _ _ name
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)).trans
  exact poolModifyFeesPreludeFrame_get _ _ _ _ name
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide)

end Benchmarks.UniswapV4PoolManager
