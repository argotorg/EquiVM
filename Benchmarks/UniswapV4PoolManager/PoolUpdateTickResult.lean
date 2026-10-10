import Benchmarks.UniswapV4PoolManager.PoolUpdateTickCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolUpdateTickPost (evm : State) (id : UInt256) (tick delta : Int) (upper : Bool) : State :=
  let packed := tickFieldWord evm id tick .liquidityPacked
  tickLiquidityStore (tickFeesPost evm id packed tick) id tick
    (EVM.wordOfInt (tickGrossAfterInt packed delta)) (tickNetAfter packed delta upper)

theorem poolUpdateTickReturnedState {f cf : Frame} {evm post : State} {id : UInt256}
    {tick delta : Int} {upper : Bool} {values : Option (List Value)}
    (h : poolUpdateTickResult f evm id tick delta upper = .returned cf post values) :
    post = poolUpdateTickPost evm id tick delta upper := by
  unfold poolUpdateTickResult poolUpdateTickFinishResult poolUpdateTickTailResult at h
  dsimp only at h
  split_ifs at h <;> cases h
  rfl

theorem poolUpdateTickReturnedValues {f cf : Frame} {evm post : State} {id : UInt256}
    {tick delta : Int} {upper : Bool} {values : Option (List Value)}
    (h : poolUpdateTickResult f evm id tick delta upper = .returned cf post values) :
    values = some [.bool (tickFlipped (tickFieldWord evm id tick .liquidityPacked) delta),
      .int (Int.ofNat (EVM.wordOfInt (tickGrossAfterInt (tickFieldWord evm id tick .liquidityPacked) delta)).toNat)] := by
  unfold poolUpdateTickResult poolUpdateTickFinishResult poolUpdateTickTailResult at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

end Benchmarks.UniswapV4PoolManager
