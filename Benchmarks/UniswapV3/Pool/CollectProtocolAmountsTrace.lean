import Benchmarks.UniswapV3.Pool.CollectProtocolPaymentTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectProtocolMin0X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw old0 old1 req0 req1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8963⟩ (old1 :: old0 :: req1 :: req0 :: R) mem aw rdata σ k C)
    (hfit : req0.toNat < 2 ^ 128) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9004⟩
      (minWord req0 (protocolFeesWord false σ ee) :: old1 :: old0 :: req1 :: req0 :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.land req0 (UInt256.ofNat (2 ^ 128 - 1)) = req0 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hf : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256))) =
      protocolFeesWord false σ ee := u256_land_comm _ _
  by_cases hgt : (protocolFeesWord false σ ee).toNat < req0.toNat
  · rw [minWord, if_pos hgt]
    obtain ⟨_, _, rdLoad⟩ := uniswapV3Pool_block_8963_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf, ugt_one hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨_, _, rdDone⟩ := uniswapV3Pool_block_8991 (immWords := wordsOf (immStore v)) (by evm_ov) rdLoad
    simp only [uniswapV3Pool_block_8991_stack, solcMask128, hf] at rdDone
    exact ⟨_, _, rdDone⟩
  · rw [minWord, if_neg hgt]
    obtain ⟨_, _, rdCopy⟩ := uniswapV3Pool_block_8963_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf]; exact ugt_zero (by omega)) rd
    have rdDone := uniswapV3Pool_block_8986 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy
    exact ⟨_, _, rdDone⟩

theorem collectProtocolMin1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw amount0 old0 old1 requested : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9004⟩ (amount0 :: old1 :: old0 :: requested :: R) mem aw rdata σ k C)
    (hfit : requested.toNat < 2 ^ 128) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9062⟩
      (minWord requested (protocolFeesWord true σ ee) :: old1 :: amount0 :: requested :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.land requested (UInt256.ofNat (2 ^ 128 - 1)) = requested := by
    rw [u256_land_comm]; exact uint128Word_clean hfit
  have hf : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac => ac.storage.getD (UInt256.ofNat 3) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) =
      protocolFeesWord true σ ee := by
    rw [solcShift128]; exact u256_land_comm _ _
  by_cases hgt : (protocolFeesWord true σ ee).toNat < requested.toNat
  · rw [minWord, if_pos hgt]
    obtain ⟨_, _, rdLoad⟩ := uniswapV3Pool_block_9004_taken (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf, ugt_one hgt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_9004_taken_stack] at rdLoad
    obtain ⟨_, _, rdDone⟩ := uniswapV3Pool_block_9042 (immWords := wordsOf (immStore v)) (by evm_ov) rdLoad
    simp only [uniswapV3Pool_block_9042_stack, solcMask128, hf] at rdDone
    exact ⟨_, _, rdDone⟩
  · rw [minWord, if_neg hgt]
    obtain ⟨_, _, rdCopy⟩ := uniswapV3Pool_block_9004_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [solcMask128, hc, hf]; exact ugt_zero (by omega)) rd
    simp only [uniswapV3Pool_block_9004_fallthrough_stack] at rdCopy
    have rdDone := uniswapV3Pool_block_9037 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy
    exact ⟨_, _, rdDone⟩

theorem collectProtocolAmountsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw old0 old1 req0 req1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8963⟩ (old1 :: old0 :: req1 :: req0 :: R) mem aw rdata σ k C)
    (hfit0 : req0.toNat < 2 ^ 128) (hfit1 : req1.toNat < 2 ^ 128) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9062⟩
      (minWord req1 (protocolFeesWord true σ ee) :: old1 ::
        minWord req0 (protocolFeesWord false σ ee) :: req1 :: req0 :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd0⟩ := collectProtocolMin0X (v := v) rd hfit0 hov
  exact collectProtocolMin1X (v := v) rd0 hfit1 (by evm_ov)

end Benchmarks.UniswapV3.Pool
