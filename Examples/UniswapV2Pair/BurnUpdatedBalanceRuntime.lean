import Examples.UniswapV2Pair.PairBalanceHeaderRuntime
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnUpdatedBalance0Prepared
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw ptr supply fee liquidity balance1 balance0 token1 token0 : UInt256}
    {R : List UInt256} {k C : Nat}
    (rd4639 : RD uniswapV2PairBytecode I g s0 ⟨4639⟩
      (supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: R) mem aw rdata acc k C)
    (hin : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size) (hlo : 96 ≤ ptr.toNat)
    (haw : aw.toNat * 32 < UInt256.size) (hawLo : 96 ≤ aw.toNat * 32)
    (hfit : ptr.toNat + 67 < UInt256.size) (hread : mem.readWithPadding 64 32 = ptr.toByteArray)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4697⟩
      (UInt256.land token0 solcAddrMask :: UInt256.land token0 solcAddrMask ::
        ptr :: ⟨36⟩ :: ptr :: ⟨32⟩ :: (ptr + ⟨36⟩) :: balanceOfSelectorWord ::
        UInt256.land token0 solcAddrMask ::
        supply :: fee :: liquidity :: balance1 :: balance0 :: token1 :: token0 :: R)
      (balanceDynamicCalldataMem mem ptr (UInt256.ofNat I.codeOwner.val))
      (balanceDynamicCalldataWords aw ptr) rdata acc k' C' := by
  have rd4640 := evm_run rd4639 with [jumpdest]
  obtain ⟨_, _, rd4662⟩ := RD.uniswapPairBalanceHeaderStored (site := .burn0) rd4640
    hin hgap hlo haw hawLo hfit hread (by simp only [List.length_cons]; omega)
  have rd4679 := evm_run rd4662 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup10, and,
    swap2, push4 balanceOfSelectorWord, swap2]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask by native_decide] at rd4679
  have rd4697 := evm_run rd4679 with [push1 ⟨36⟩, dup1, dup4, add, swap3, push1 ⟨32⟩,
    swap3, swap2, swap1, dup3, swap1, sub, add, dup2, dup7, dup1]
  rw [u256_sub_self, show (⟨0⟩ : UInt256) + ⟨36⟩ = ⟨36⟩ by native_decide] at rd4697
  exact ⟨_, _, rd4697⟩

end UniswapV2Pair
