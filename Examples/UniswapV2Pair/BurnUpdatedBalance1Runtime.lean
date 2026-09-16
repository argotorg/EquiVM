import Examples.UniswapV2Pair.BurnUpdatedBalanceRuntime
import Examples.UniswapV2Pair.StackRoutines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdatedBalance1Prepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr supply fee liquidity balance1 balance0 newBalance0 token1 token0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd4754 : RD uniswapV2PairBytecode I g s0 ⟨4754⟩
      (newBalance0 :: supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4815⟩
      (UInt256.land token1 solcAddrMask :: UInt256.land token1 solcAddrMask ::
        ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord ::
        UInt256.land token1 solcAddrMask ::
        supply :: fee :: liquidity :: balance1 :: newBalance0 :: token1 :: token0 :: R)
      (balanceDynamicCalldataMem mem ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata acc k' C' := by
  obtain ⟨_, _, rd4776⟩ := RD.uniswapPairBalanceHeaderStored (site := .burn1) rd4754
    hin hgap hlo haw hawLo hfit hread (by simp only [List.length_cons]; omega)
  have rd4796 := evm_run rd4776 with [swap2, swap7, pop, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup9, and,
    swap2, push4 balanceOfSelectorWord, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask by native_decide] at rd4796
  have rd4815 := evm_run rd4796 with [push1 ⟨36⟩, dup1, dup3, add, swap3, push1 ⟨32⟩,
    swap3, swap1, swap2, swap1, dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [u256_sub_self, show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ by native_decide] at rd4815
  exact ⟨_, _, rd4815⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdateEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {mem rdata : ByteArray}
    {aw newBalance1 supply fee liquidity balance1 newBalance0 token1 token0 reserve1 reserve0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd4872 : RD uniswapV2PairBytecode I g s0 ⟨4872⟩
      (newBalance1 :: supply :: fee :: liquidity :: balance1 :: newBalance0 :: token1 :: token0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k C) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6959⟩
      (reserve1 :: reserve0 :: newBalance1 :: newBalance0 :: ⟨4885⟩ ::
        supply :: fee :: liquidity :: newBalance1 :: newBalance0 :: token1 :: token0 :: reserve1 :: reserve0 :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd4872 with [swap4, pop, push2 ⟨4885⟩, dup6, dup6, dup12, dup12,
    push2 ⟨6959⟩, jump (by jump_dest)]⟩

end UniswapV2Pair
