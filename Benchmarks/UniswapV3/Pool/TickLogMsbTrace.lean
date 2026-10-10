import Benchmarks.UniswapV3.Pool.TickLogMsbPrefixTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogMsbFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ratio price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14216⟩
      (tickLogMsbPrefixStack ratio price R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14273⟩
      (UInt256.ofNat (tickLogMsbCount ratio) :: tickLogNormalized ratio (tickLogMsbCount ratio) ::
        ratio :: ⟨0⟩ :: price :: R) mem aw rdata σ k' C' := by
  have h6 : UInt256.shiftLeft (UInt256.gt (tickLogMsbScan ratio 6) (UInt256.ofNat 3))
      (UInt256.ofNat 1) = tickLogMsbPart ratio 6 :=
    tickLogMsbChoice_eq _ 1 (by decide)
  have hr6 : UInt256.shiftRight (tickLogMsbScan ratio 6) (tickLogMsbPart ratio 6) =
      tickLogMsbScan ratio 7 := rfl
  have h7 : UInt256.gt (tickLogMsbScan ratio 7) (UInt256.ofNat 1) = tickLogMsbPart ratio 7 :=
    tickLogMsbChoiceLast_eq _
  have hm := (tickLogMsbPack_eq ratio).1
  dsimp only [tickLogMsbPack] at hm
  have hmword : (UInt256.ofNat (tickLogMsbCount ratio)).toNat = tickLogMsbCount ratio :=
    UInt256.toNat_ofNat_of_lt (lt_trans (tickLogMsbPack_eq ratio).2 (by decide))
  unfold tickLogMsbPrefixStack at rd
  by_cases h : 128 ≤ tickLogMsbCount ratio
  · have hlt : UInt256.lt (UInt256.ofNat (tickLogMsbCount ratio)) (UInt256.ofNat 128) = ⟨0⟩ :=
      ult_zero (by rw [hmword]; exact h)
    have r1 := uniswapV3Pool_block_14216_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [h6, hr6, h7, hm]; exact hlt) rd
    have rmsb : RD (deployedRuntime v) ee g s0 ⟨14250⟩
        (UInt256.ofNat (tickLogMsbCount ratio) :: tickLogMsbScan ratio 7 ::
          ratio :: ⟨0⟩ :: price :: R) mem aw rdata σ (k + 30) (C + 97) := by
      simpa only [uniswapV3Pool_block_14216_fallthrough_stack, h6, hr6, h7, hm] using r1
    have r2 := uniswapV3Pool_block_14250 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rmsb
    refine ⟨k + 30 + 10, C + 97 + 34, ?_⟩
    simpa only [uniswapV3Pool_block_14250_stack, tickLogNormalized, if_pos h] using r2
  · have hlt : UInt256.lt (UInt256.ofNat (tickLogMsbCount ratio)) (UInt256.ofNat 128) = ⟨1⟩ :=
      ult_one (by rw [hmword]; exact Nat.lt_of_not_ge h)
    have r1 := uniswapV3Pool_block_14216_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [h6, hr6, h7, hm, hlt]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rmsb : RD (deployedRuntime v) ee g s0 ⟨14263⟩
        (UInt256.ofNat (tickLogMsbCount ratio) :: tickLogMsbScan ratio 7 ::
          ratio :: ⟨0⟩ :: price :: R) mem aw rdata σ (k + 30) (C + 97) := by
      simpa only [uniswapV3Pool_block_14216_taken_stack, h6, hr6, h7, hm] using r1
    have r2 := uniswapV3Pool_block_14263 (immWords := wordsOf (immStore v)) (by evm_ov) rmsb
    refine ⟨k + 30 + 9, C + 97 + 24, ?_⟩
    simpa only [uniswapV3Pool_block_14263_stack, tickLogNormalized, if_neg h] using r2

theorem tickLogMsbX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14102⟩ (⟨0⟩ :: price :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14273⟩
      (UInt256.ofNat (tickLogMsb (tickLogPrice price)).1 ::
        tickLogNormalized (tickLogRatio (tickLogPrice price)) (tickLogMsb (tickLogPrice price)).1 ::
        tickLogRatio (tickLogPrice price) :: ⟨0⟩ :: price :: R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', r1⟩ := tickLogMsbPrefixX rd (by omega)
  simpa only [tickLogMsb_eq] using tickLogMsbFinishX r1 hov

end Benchmarks.UniswapV3.Pool
