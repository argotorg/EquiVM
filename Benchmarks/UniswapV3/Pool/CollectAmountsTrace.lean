import Benchmarks.UniswapV3.Pool.CollectPaymentsSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionOwedWord_evm0 (key : UInt256) (σ : AccountMap) (ee : ExecutionEnv) :
    UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee) =
      positionOwedWord key false σ ee := by
  unfold positionOwedWord positionFieldWord
  change _ = UInt256.land (UInt256.div _ ⟨1⟩) (UInt256.ofNat (2 ^ 128 - 1))
  rw [u256_div_one, u256_land_comm]

theorem positionOwedWord_evm1 (key : UInt256) (σ : AccountMap) (ee : ExecutionEnv) :
    UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (UInt256.div (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) =
      positionOwedWord key true σ ee := by
  rw [solcShift128, u256_land_comm]
  rfl

theorem collectMin0X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw key junk old0 old1 req0 req1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7652⟩
      (solcMappingSlot ⟨7⟩ key :: junk :: old1 :: old0 :: req1 :: req0 :: R) mem aw rdata σ k C)
    (hfit : req0.toNat < 2 ^ 128) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7700⟩
      (minWord req0 (positionOwedWord key false σ ee) :: solcMappingSlot ⟨7⟩ key ::
        old1 :: old0 :: req1 :: req0 :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land req0 (UInt256.ofNat (2 ^ 128 - 1)) = req0 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hf := positionOwedWord_evm0 key σ ee
  unfold solcSlotWordAt at hf
  by_cases hgt : (positionOwedWord key false σ ee).toNat < req0.toNat
  · rw [minWord, if_pos hgt]
    obtain ⟨_, _, rdLoad⟩ := uniswapV3Pool_block_7652_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf, ugt_one hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_7652_taken_stack] at rdLoad
    obtain ⟨_, _, rdDone⟩ := uniswapV3Pool_block_7685 (immWords := wordsOf (immStore v)) (by evm_ov) rdLoad
    simp only [uniswapV3Pool_block_7685_stack, solcMask128, hf] at rdDone
    exact ⟨_, _, rdDone⟩
  · rw [minWord, if_neg hgt]
    obtain ⟨_, _, rdCopy⟩ := uniswapV3Pool_block_7652_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf]; exact ugt_zero (by omega)) rd
    simp only [uniswapV3Pool_block_7652_fallthrough_stack] at rdCopy
    have rdDone := uniswapV3Pool_block_7680 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy
    exact ⟨_, _, rdDone⟩

theorem collectMin1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw key amount0 old0 old1 requested : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7700⟩
      (amount0 :: solcMappingSlot ⟨7⟩ key :: old1 :: old0 :: requested :: R) mem aw rdata σ k C)
    (hfit : requested.toNat < 2 ^ 128) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7762⟩
      (minWord requested (positionOwedWord key true σ ee) :: solcMappingSlot ⟨7⟩ key ::
        old1 :: amount0 :: requested :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land requested (UInt256.ofNat (2 ^ 128 - 1)) = requested := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hf := positionOwedWord_evm1 key σ ee
  unfold solcSlotWordAt at hf
  by_cases hgt : (positionOwedWord key true σ ee).toNat < requested.toNat
  · rw [minWord, if_pos hgt]
    obtain ⟨_, _, rdLoad⟩ := uniswapV3Pool_block_7700_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf, ugt_one hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_7700_taken_stack] at rdLoad
    obtain ⟨_, _, rdDone⟩ := uniswapV3Pool_block_7740 (immWords := wordsOf (immStore v)) (by evm_ov) rdLoad
    simp only [uniswapV3Pool_block_7740_stack, solcMask128, hf] at rdDone
    exact ⟨_, _, rdDone⟩
  · rw [minWord, if_neg hgt]
    obtain ⟨_, _, rdCopy⟩ := uniswapV3Pool_block_7700_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf]; exact ugt_zero (by omega)) rd
    simp only [uniswapV3Pool_block_7700_fallthrough_stack] at rdCopy
    have rdDone := uniswapV3Pool_block_7735 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy
    exact ⟨_, _, rdDone⟩

theorem collectAmountsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw key junk old0 old1 req0 req1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨7652⟩
      (solcMappingSlot ⟨7⟩ key :: junk :: old1 :: old0 :: req1 :: req0 :: R) mem aw rdata σ k C)
    (hfit0 : req0.toNat < 2 ^ 128) (hfit1 : req1.toNat < 2 ^ 128) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨7762⟩
      (minWord req1 (positionOwedWord key true σ ee) :: solcMappingSlot ⟨7⟩ key ::
        old1 :: minWord req0 (positionOwedWord key false σ ee) :: req1 :: req0 :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd0⟩ := collectMin0X (v := v) rd hfit0 hov
  exact collectMin1X (v := v) rd0 hfit1 (by evm_ov)

end Benchmarks.UniswapV3.Pool
