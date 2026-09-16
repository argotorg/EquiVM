import Examples.UniswapV2Pair.SwapReserveGuardRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapAmountInWord (balance reserve amountOut : UInt256) : UInt256 :=
  if (UInt256.sub reserve amountOut).toNat < balance.toNat then
    UInt256.sub balance (UInt256.sub reserve amountOut) else ⟨0⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapInputDifference
    {g : Sat256} {s0 : State} {I : ExecutionEnv} {second : Bool}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw balance reserve amountOut x0 x1 x3 x5 x6 x7 x8 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd : RD uniswapV2PairBytecode I g s0 (if second then ⟨2400⟩ else ⟨2356⟩)
      (x0 :: x1 :: balance :: x3 :: reserve :: x5 :: x6 :: x7 :: x8 :: amountOut :: R)
      mem aw rdata acc k C)
    (hclean : UInt256.land reserve reserve112Mask = reserve)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 (if second then ⟨2415⟩ else ⟨2371⟩)
      (UInt256.sub balance (UInt256.sub reserve amountOut) ::
        x0 :: x1 :: balance :: x3 :: reserve :: x5 :: x6 :: x7 :: x8 :: amountOut :: R)
      mem aw rdata acc k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask := by native_decide
  cases second <;>
    (have rd' := evm_run rd with [jumpdest, dup10, dup6, push1 ⟨1⟩, push1 ⟨1⟩,
      push1 ⟨112⟩, shl, sub, and, sub, dup4, sub]
     rw [hmask, u256_land_comm reserve112Mask, hclean] at rd'
     exact ⟨_, _, rd'⟩)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapAmount0In
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw balance1 balance0 reserve1 reserve0 dataLen dataPtr
      toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd2331 : RD uniswapV2PairBytecode I g s0 ⟨2331⟩
      (⟨0⟩ :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2374⟩
      (swapAmountInWord balance0 reserve0 amount0Out :: balance1 :: balance0 :: reserve1 :: reserve0 ::
        dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C' := by
  have rd2349 := evm_run rd2331 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub,
    dup6, and, dup11, swap1, sub, dup4, gt, push2 ⟨2356⟩]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask by native_decide,
    hclean0] at rd2349
  by_cases hp : (UInt256.sub reserve0 amount0Out).toNat < balance0.toNat
  · rw [ugt_one hp] at rd2349
    have rd2356 := evm_run rd2349 with [jumpiT (by decide) (by jump_dest)]
    obtain ⟨_, _, rd2371⟩ := RD.uniswapSwapInputDifference (second := false) rd2356 hclean0 (by omega)
    have rd2374 := evm_run rd2371 with [jumpdest, swap1, pop]
    simpa only [swapAmountInWord, if_pos hp] using ⟨_, _, rd2374⟩
  · rw [ugt_zero (by exact Nat.le_of_not_lt hp)] at rd2349
    have rd2374 := evm_run rd2349 with [jumpiNT (by decide), push1 ⟨0⟩, push2 ⟨2371⟩,
      jump (by jump_dest), jumpdest, swap1, pop]
    simpa only [swapAmountInWord, if_neg hp] using ⟨_, _, rd2374⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapAmount1In
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw amount0In balance1 balance0 reserve1 reserve0 dataLen dataPtr
      toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd2374 : RD uniswapV2PairBytecode I g s0 ⟨2374⟩
      (amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2418⟩
      (swapAmountInWord balance1 reserve1 amount1Out :: amount0In :: balance1 :: balance0 :: reserve1 :: reserve0 ::
        dataLen :: dataPtr :: toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C' := by
  have rd2393 := evm_run rd2374 with [push1 ⟨0⟩, dup10, dup6, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨112⟩, shl, sub, and, sub, dup4, gt, push2 ⟨2400⟩]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask by native_decide,
    u256_land_comm reserve112Mask, hclean1] at rd2393
  by_cases hp : (UInt256.sub reserve1 amount1Out).toNat < balance1.toNat
  · rw [ugt_one hp] at rd2393
    have rd2400 := evm_run rd2393 with [jumpiT (by decide) (by jump_dest)]
    obtain ⟨_, _, rd2415⟩ := RD.uniswapSwapInputDifference (second := true) rd2400 hclean1
      (by simp only [List.length_cons]; omega)
    have rd2418 := evm_run rd2415 with [jumpdest, swap1, pop]
    simpa only [swapAmountInWord, if_pos hp] using ⟨_, _, rd2418⟩
  · rw [ugt_zero (by exact Nat.le_of_not_lt hp)] at rd2393
    have rd2418 := evm_run rd2393 with [jumpiNT (by decide), push1 ⟨0⟩, push2 ⟨2415⟩,
      jump (by jump_dest), jumpdest, swap1, pop]
    simpa only [swapAmountInWord, if_neg hp] using ⟨_, _, rd2418⟩

end UniswapV2Pair
