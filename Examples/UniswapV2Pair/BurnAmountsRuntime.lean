import Examples.UniswapV2Pair.BurnBeforeFeeSource
import Examples.UniswapV2Pair.Invalid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeTotalSupplyLoaded
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem rdata : ByteArray} {aw feeOn : UInt256} {R : List UInt256} {k C : ℕ}
    (rd4472 : RD uniswapV2PairBytecode I g s0 ⟨4472⟩ (feeOn :: ⟨0⟩ :: R)
      mem aw rdata (cA, σ) k C) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4479⟩
      (uniswapSlotWord ⟨0⟩ σ I :: feeOn :: R) mem aw rdata (cA, σ) k' C' := by
  have rd4475 := evm_run rd4472 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨_, _, rd4476⟩ := rd4475.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4479 := evm_run rd4476 with [swap1, swap2, pop]
  exact ⟨_, _, rd4479⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount0MulEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw totalSupply feeOn liquidity balance0 balance1 : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd4479 : RD uniswapV2PairBytecode I g s0 ⟨4479⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6780⟩
      (balance0 :: liquidity :: ⟨4495⟩ :: totalSupply :: totalSupply :: feeOn :: liquidity ::
        balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
  have rd := evm_run rd4479 with [dup1, push2 ⟨4495⟩, dup5, dup8,
    push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide] at rd
  exact ⟨_, _, rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount1MulEntry
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw totalSupply feeOn liquidity balance0 balance1 : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd4506 : RD uniswapV2PairBytecode I g s0 ⟨4506⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: R) mem aw rdata acc k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨6780⟩
      (balance1 :: liquidity :: ⟨4522⟩ :: totalSupply :: totalSupply :: feeOn :: liquidity ::
        balance1 :: balance0 :: R) mem aw rdata acc k' C' := by
  have rd := evm_run rd4506 with [dup1, push2 ⟨4522⟩, dup5, dup7,
    push4 ⟨0xffffffff⟩, push2 ⟨6780⟩, and]
  rw [show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ from by decide] at rd
  exact ⟨_, _, rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount0DivSuccess
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product totalSupply : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4495⟩ (product :: totalSupply :: R)
      mem aw rdata acc k C)
    (hnonzero : totalSupply ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4504⟩
      (UInt256.div product totalSupply :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, dup2, push2 ⟨4502⟩,
    jumpiT hnonzero (by jump_dest), jumpdest, div]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount0DivZero
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4495⟩ (product :: ⟨0⟩ :: R)
      mem aw rdata acc k C) (hov : R.length + 6 ≤ 1024) :
    RDinvalid uniswapV2PairBytecode g s0 := by
  have rdInvalid := evm_run rd with [jumpdest, dup2, push2 ⟨4502⟩,
    jumpiNT (by native_decide)]
  exact RD.invalidHalt rdInvalid (by native_decide)

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount1DivSuccess
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product totalSupply : UInt256}
    {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4522⟩ (product :: totalSupply :: R)
      mem aw rdata acc k C)
    (hnonzero : totalSupply ≠ ⟨0⟩) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4531⟩
      (UInt256.div product totalSupply :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, dup2, push2 ⟨4529⟩,
    jumpiT hnonzero (by jump_dest), jumpdest, div]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount1DivZero
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4522⟩ (product :: ⟨0⟩ :: R)
      mem aw rdata acc k C) (hov : R.length + 6 ≤ 1024) :
    RDinvalid uniswapV2PairBytecode g s0 := by
  have rdInvalid := evm_run rd with [jumpdest, dup2, push2 ⟨4529⟩,
    jumpiNT (by native_decide)]
  exact RD.invalidHalt rdInvalid (by native_decide)

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount0Computed
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4495⟩
      (product :: totalSupply :: totalSupply :: feeOn :: liquidity :: balance1 :: balance0 ::
        token1 :: token0 :: reserve1 :: reserve0 :: ⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata acc k C)
    (hnonzero : totalSupply ≠ ⟨0⟩) (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4506⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: ⟨0⟩ :: UInt256.div product totalSupply :: R) mem aw rdata acc k' C' := by
  obtain ⟨_, _, rdDiv⟩ := uniswapBurnRuntimeAmount0DivSuccess rd hnonzero
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rdDiv with [swap11, pop]⟩

set_option maxHeartbeats 1000000 in
theorem uniswapBurnRuntimeAmount1Computed
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw product totalSupply feeOn liquidity balance0 balance1
      token0 token1 reserve0 reserve1 amount0 : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4522⟩
      (product :: totalSupply :: totalSupply :: feeOn :: liquidity :: balance1 :: balance0 ::
        token1 :: token0 :: reserve1 :: reserve0 :: ⟨0⟩ :: amount0 :: R) mem aw rdata acc k C)
    (hnonzero : totalSupply ≠ ⟨0⟩) (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4533⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: UInt256.div product totalSupply :: amount0 :: R) mem aw rdata acc k' C' := by
  obtain ⟨_, _, rdDiv⟩ := uniswapBurnRuntimeAmount1DivSuccess rd hnonzero
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rdDiv with [swap10, pop]⟩

end UniswapV2Pair
