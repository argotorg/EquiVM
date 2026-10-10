import Benchmarks.UniswapV4PoolManager.LPFeeSource
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_033
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem decodeFee164Trace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨11887⟩ (ret :: R) mem aw rdata σ k C) :
    ((calldataWord I.calldata 164).toNat < 2^24 ∧
      ∃ k' C', RD (deployedRuntime v) I g s0 ret (calldataWord I.calldata 164 :: R) mem aw rdata σ k' C') ∨
    (¬(calldataWord I.calldata 164).toNat < 2^24 ∧ RDrev (deployedRuntime v) g s0) := by
  by_cases hf : (calldataWord I.calldata 164).toNat < 2^24
  · refine .inl ⟨hf, ?_⟩
    have hc : UInt256.land (calldataWord I.calldata 164) (UInt256.ofNat 16777215) =
        calldataWord I.calldata 164 := u256LandMaskCleanOfToNat _ _ rfl hf
    have rd1 := poolManagerBlocks.poolManager_block_11887_fallthrough hstack
      (u256_sub_eq_zero_iff_eq.mpr hc.symm) h
    have rd2 := poolManagerBlocks.poolManager_block_11904 (by simp; omega) hret rd1
    exact ⟨_, _, rd2⟩
  · refine .inr ⟨hf, ?_⟩
    have hc : UInt256.sub (calldataWord I.calldata 164)
        (UInt256.land (calldataWord I.calldata 164) (UInt256.ofNat 16777215)) ≠ ⟨0⟩ := by
      apply u256_sub_ne_zero_of_ne
      exact fun he => hf ((landMask_eq_iff _ _ rfl).1 he.symm)
    have rd1 := poolManagerBlocks.poolManager_block_11887_taken hstack hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact emptyRevert v (by change R.length+4 ≤ 1024; exact hstack) rd1

theorem lpFeeValidateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret fee : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+4 ≤ 1024) (hc : fee.toNat < 2^24)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13966⟩ (fee :: ret :: R) mem aw rdata σ k C) :
    if fee.toNat ≤ 1000000 then ∃ k' C', RD (deployedRuntime v) I g s0 ret R mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hclean : UInt256.land (UInt256.ofNat 16777215) fee = fee :=
    (u256_land_comm _ _).trans (u256LandMaskCleanOfToNat _ _ rfl hc)
  by_cases hv : fee.toNat ≤ 1000000
  · rw [if_pos hv]
    have rd1 := poolManagerBlocks.poolManager_block_13966_fallthrough (by simp; omega)
      (by rw [hclean]; exact ugt_zero hv) h
    have rd2 := poolManagerBlocks.poolManager_block_13982 (by simp; omega) hret rd1
    exact ⟨_, _, rd2⟩
  · rw [if_neg hv]
    have rd1 := poolManagerBlocks.poolManager_block_13966_taken (by simp; omega)
      (by rw [hclean, ugt_one (Nat.lt_of_not_ge hv)]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact poolManagerBlocks.poolManager_block_13984 (by simp; omega) rd1

end Benchmarks.UniswapV4PoolManager
