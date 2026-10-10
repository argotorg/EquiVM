import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTickFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolModifyTickResultTrace {code : ByteArray} {g : Sat256} {s0 evm : State}
    {f : Frame} {id : UInt256} {tick delta : Int} {upper fl fu : Bool} {gl gu : UInt256}
    {onReturn : State → Option (List Value) → Prop}
    (hr : functionResultTrace code g s0 onReturn
      (poolUpdateTickResult (poolModifyTickAliasFrame f id upper) evm id tick delta upper)) :
    blockResultTrace code g s0 (fun _ post => onReturn post (some
      [.bool (tickFlipped (tickFieldWord evm id tick .liquidityPacked) delta),
       .int (Int.ofNat (EVM.wordOfInt (tickGrossAfterInt (tickFieldWord evm id tick .liquidityPacked) delta)).toNat)]))
      (fun _ _ => False) (poolModifyTickResult f evm id tick delta upper fl gl fu gu) := by
  apply blockResultTrace_continueCall hr
  intro cf post values hv ht
  rw [poolUpdateTickReturnedValues hv] at ht
  exact ht

end Benchmarks.UniswapV4PoolManager
