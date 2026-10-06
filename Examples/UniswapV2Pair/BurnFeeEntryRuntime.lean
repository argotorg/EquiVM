import Examples.UniswapV2Pair.MintFeeCallRuntimeCases
import Examples.UniswapV2Pair.BurnInternalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeMintFeeEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {σ : AccountMap}
    {mem rdata : ByteArray} {balance0 balance1 token0 token1 reserve0 reserve1 : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd4444 : RD uniswapV2PairBytecode I g s0 ⟨4444⟩
      (balance1 :: ⟨0⟩ :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 :: R)
      mem feeToStaticcallActiveWords rdata σ k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨7696⟩
      (reserve1 :: reserve0 :: ⟨4472⟩ :: ⟨0⟩ ::
        uniswapCodeOwnerStorageWord I σ
          (uniswapInternalMintBalanceHashSlot (UInt256.ofNat I.codeOwner.val) mem) ::
        balance1 :: balance0 :: token1 :: token0 :: reserve1 :: reserve0 :: R)
      (uniswapInternalMintBalanceHashMem (UInt256.ofNat I.codeOwner.val) mem)
      feeToStaticcallActiveWords rdata σ k' C' := by
  have hclean := codeOwnerWord_clean I
  have rd4449 := evm_run rd4444 with [address, push1 ⟨0⟩, swap1, dup2]
  have rd4450 := rd4449.mstore 0
    (wordAt0Mem (UInt256.ofNat I.codeOwner.val) mem) feeToStaticcallActiveWords
    (by native_decide) mem_cost rfl (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4454 := evm_run rd4450 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd4455 := rd4454.mstore 0
    (uniswapInternalMintBalanceHashMem (UInt256.ofNat I.codeOwner.val) mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost
    (by simp only [uniswapInternalMintBalanceHashMem, hclean]; rfl)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd4458 := evm_run rd4455 with [push1 ⟨64⟩, dup2]
  have rd4459 := rd4458.keccak256 0
    (uniswapInternalMintBalanceHashSlot (UInt256.ofNat I.codeOwner.val) mem)
    feeToStaticcallActiveWords (by native_decide) mem_cost rfl (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4460⟩ := rd4459.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd7696 := evm_run rd4460 with [swap2, swap3, pop,
    push2 ⟨4472⟩, dup9, dup9, push2 ⟨7696⟩, jump (by jump_dest)]
  exact ⟨_, _, rd7696⟩

end UniswapV2Pair
