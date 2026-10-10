import Benchmarks.UniswapV4PoolManager.PoolSwapFeeWords
import Benchmarks.UniswapV4PoolManager.MemoryGas
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_056
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_058

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapProtocolMemory (mem : ByteArray) (step : UInt256) (s : PoolSwapStepWords)
    (fee protocol : UInt256) : ByteArray :=
  if protocol = ⟨0⟩ then mem
  else (UInt256.sub s.feeAmount (poolSwapProtocolShare s fee protocol)).toByteArray.write
    0 mem (step+UInt256.ofNat 192).toNat 32

def poolSwapProtocolActiveAW (aw step fee protocol : UInt256) : UInt256 :=
  M (if fee = protocol then aw else M aw (step+UInt256.ofNat 128) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩

def poolSwapProtocolAW (aw step fee protocol : UInt256) : UInt256 :=
  if protocol = ⟨0⟩ then aw else poolSwapProtocolActiveAW aw step fee protocol

theorem poolSwapProtocolTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw step fee protocol amount tag x1 params remaining calculated dir : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+15 ≤ 1024)
    (hfc : fee.toNat < 2^24) (hpc : protocol.toNat < 2^16)
    (hi : memLoad (step+UInt256.ofNat 128) mem = s.amountIn)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (h : RD (deployedRuntime v) I g s0 ⟨19794⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19804⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, poolSwapProtocolAmount s fee protocol amount, dir, step] ++ R)
      (poolSwapProtocolMemory mem step s fee protocol) (poolSwapProtocolAW aw step fee protocol) rdata σ k' C' := by
  have hfm : UInt256.land fee (UInt256.ofNat 16777215) = fee := u256LandMaskCleanOfToNat _ _ rfl hfc
  have hpm : UInt256.land protocol (UInt256.ofNat 65535) = protocol := u256LandMaskCleanOfToNat _ _ rfl hpc
  by_cases hz : protocol = ⟨0⟩
  · have rd := poolManagerBlocks.poolManager_block_19794_fallthrough
      (by change R.length+3+9 ≤ 1024; omega) (by rw [hpm, hz]; rfl) h
    simp only [poolSwapProtocolAmount, poolSwapProtocolMemory, poolSwapProtocolAW, if_pos hz]
    exact ⟨_, _, by omega, rd⟩
  · have rd0 := poolManagerBlocks.poolManager_block_19794_taken
      (by change R.length+3+9 ≤ 1024; omega) (by rwa [hpm])
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hshare : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨20272⟩
        ([amount, poolSwapProtocolShare s fee protocol, x1, params, remaining, calculated,
          fee, protocol, tag, dir, step] ++ R)
        mem (poolSwapProtocolActiveAW aw step fee protocol) rdata σ k' C' := by
      by_cases he : fee = protocol
      · have rd1 := poolManagerBlocks.poolManager_block_20248_fallthrough
          (by change R.length+2+11 ≤ 1024; omega)
          (by rw [hpm, hfm, he]; exact u256_sub_eq_zero_iff_eq.mpr rfl) rd0
        simp only [poolManagerBlocks.poolManager_block_20248_fallthrough_stack] at rd1
        have rd2 := poolManagerBlocks.poolManager_block_20266 (by change R.length+12 ≤ 1024; omega) rd1
        simp only [poolManagerBlocks.poolManager_block_20266_stack, hf] at rd2
        simp only [poolSwapProtocolShare, poolSwapProtocolActiveAW, if_pos he]
        exact ⟨_, _, by omega, rd2⟩
      · have rd1 := poolManagerBlocks.poolManager_block_20248_taken
          (by change R.length+2+11 ≤ 1024; omega)
          (by rw [hpm, hfm]; exact fun hzero => he (u256_sub_eq_zero_iff_eq.mp hzero).symm)
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd0
        simp only [poolManagerBlocks.poolManager_block_20248_taken_stack] at rd1
        have rd2 := poolManagerBlocks.poolManager_block_20291 hstack
          (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
        simp only [poolManagerBlocks.poolManager_block_20291_stack, hi, hf, hpm, u256_add_comm s.feeAmount s.amountIn] at rd2
        simp only [poolSwapProtocolShare, poolSwapProtocolActiveAW, if_neg he]
        exact ⟨_, _, by omega, rd2⟩
    obtain ⟨k', C', hC, rd⟩ := hshare
    have rd' := poolManagerBlocks.poolManager_block_20272 (by change R.length+14 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [poolManagerBlocks.poolManager_block_20272_stack, poolManagerBlocks.poolManager_block_20272_memory,
      hf, poolSwapProtocolActiveAW, memoryWords_idem] at rd'
    simp only [poolSwapProtocolAmount, poolSwapProtocolMemory, poolSwapProtocolAW, poolSwapProtocolActiveAW, if_neg hz]
    exact ⟨_, _, by omega, rd'⟩

end Benchmarks.UniswapV4PoolManager
