import Benchmarks.UniswapV4PoolManager.PositionUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def positionUpdateOwed (evm : State) (id key : UInt256) (delta : Int) (fee : UInt256) (second : Bool) : UInt256 :=
  let liquidity := positionLiquidityWord evm id key
  positionFeesOwed (positionChangeState evm id key liquidity delta) id key liquidity fee second
def positionUpdatePost (evm : State) (id key : UInt256) (delta : Int) (fee0 fee1 : UInt256) : State :=
  positionFeeStores (positionChangeState evm id key (positionLiquidityWord evm id key) delta) id key fee0 fee1

theorem positionUpdateReturnedValues {f cf : Frame} {evm post : State} {id key fee0 fee1 : UInt256}
    {delta : Int} {values : Option (List Value)}
    (h : positionUpdateResult f evm id key delta fee0 fee1 = .returned cf post values) :
    values = some [.int (Int.ofNat (positionUpdateOwed evm id key delta fee0 false).toNat),
      .int (Int.ofNat (positionUpdateOwed evm id key delta fee1 true).toNat)] := by
  unfold positionUpdateResult positionFeesResult positionFeesStoreResult at h
  dsimp only at h
  split_ifs at h <;> cases h
  rfl

theorem positionUpdateReturnedState {f cf : Frame} {evm post : State} {id key fee0 fee1 : UInt256}
    {delta : Int} {values : Option (List Value)}
    (h : positionUpdateResult f evm id key delta fee0 fee1 = .returned cf post values) :
    post = positionUpdatePost evm id key delta fee0 fee1 := by
  unfold positionUpdateResult positionFeesResult positionFeesStoreResult at h
  dsimp only at h
  split_ifs at h <;> cases h
  rfl

end Benchmarks.UniswapV4PoolManager
