import Examples.UniswapV2Pair.PairBalanceHeaderRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapBalance0Prepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd2091 : RD uniswapV2PairBytecode I g s0 ⟨2091⟩
      (token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2149⟩
      (UInt256.land token0 solcAddrMask :: UInt256.land token0 solcAddrMask ::
        ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: UInt256.land token0 solcAddrMask ::
        token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R)
      (balanceDynamicCalldataMem mem ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata acc k' C' := by
  have rd2092 := evm_run rd2091 with [jumpdest]
  obtain ⟨_, _, rd2114⟩ := RD.uniswapPairBalanceHeaderStored (site := .swap0) rd2092
    hin hgap hlo haw hawLo hfit hread (by simp only [List.length_cons]; omega)
  have rd2131 := evm_run rd2114 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    swap2, push4 balanceOfSelectorWord, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask by native_decide] at rd2131
  have rd2149 := evm_run rd2131 with [push1 ⟨36⟩, dup1, dup4, add, swap3, push1 ⟨32⟩,
    swap3, swap2, swap1, dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [u256_sub_self, show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ by native_decide] at rd2149
  exact ⟨_, _, rd2149⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapBalance1Prepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr newBalance0 token1 token0 scratch1 scratch0 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd2206 : RD uniswapV2PairBytecode I g s0 ⟨2206⟩
      (newBalance0 :: token1 :: token0 :: scratch1 :: scratch0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2267⟩
      (UInt256.land token1 solcAddrMask :: UInt256.land token1 solcAddrMask ::
        ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord :: UInt256.land token1 solcAddrMask ::
        token1 :: token0 :: scratch1 :: newBalance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R)
      (balanceDynamicCalldataMem mem ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata acc k' C' := by
  obtain ⟨_, _, rd2228⟩ := RD.uniswapPairBalanceHeaderStored (site := .swap1) rd2206
    hin hgap hlo haw hawLo hfit hread (by simp only [List.length_cons]; omega)
  have rd2248 := evm_run rd2228 with [swap2, swap6, pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    swap2, push4 balanceOfSelectorWord, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask by native_decide] at rd2248
  have rd2267 := evm_run rd2248 with [push1 ⟨36⟩, dup1, dup3, add, swap3, push1 ⟨32⟩,
    swap3, swap1, swap2, swap1, dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [u256_sub_self, show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ by native_decide] at rd2267
  exact ⟨_, _, rd2267⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSwapBalancesExit
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw balance1 balance0 token1 token0 scratch1 reserve1 reserve0
      dataLen dataPtr toWord amount1Out amount0Out : UInt256} {R : List UInt256} {k C : Nat}
    (rd2324 : RD uniswapV2PairBytecode I g s0 ⟨2324⟩
      (balance1 :: token1 :: token0 :: scratch1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨2331⟩
      (⟨0⟩ :: balance1 :: balance0 :: reserve1 :: reserve0 :: dataLen :: dataPtr ::
        toWord :: amount1Out :: amount0Out :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd2324 with [swap3, pop, push1 ⟨0⟩, swap2, pop, pop]⟩

end UniswapV2Pair
