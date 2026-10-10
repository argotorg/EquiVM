import Benchmarks.UniswapV4PoolManager.AfterInitializeEncodeTrace
import Benchmarks.UniswapV4PoolManager.AllocationTrace
import Benchmarks.UniswapV4PoolManager.HookCallTrace
import Benchmarks.UniswapV4PoolManager.InitializeReturnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem afterInitializeActiveTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr price tick junk : UInt256}
    {key : PoolKeyWords} {hook : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+323 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4611⟩
      (accountWord hook :: keyPtr :: price :: tick :: ⟨32⟩ :: junk :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out, callViaEVM evm hook 0 (afterInitializePayload I.source key price tick) (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (if z = true ∧ hookReplyValid (afterInitializePayload I.source key price tick) out then
        RDret (deployedRuntime v) g s0 evm'.accountMap tick.toByteArray
      else RDrev (deployedRuntime v) g s0) := by
  have hf256 : free.toNat+1024 < UInt256.size := by
    have hmax : solcMaxU64+1024 < UInt256.size := by decide
    omega
  obtain ⟨aw1, k1, C1, rd1⟩ := afterInitializeEncodeTrace v
    (by simp only [List.length_cons]; omega) hv hc hb (by omega) hfree h
  obtain ⟨aw2, k2, C2, rd2⟩ := allocateTrace v (by simp only [List.length_cons]; omega) hf
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hend : allocationEnd free (UInt256.ofNat 292) = free+⟨320⟩ := by
    unfold allocationEnd
    congr 1
  rw [hend] at rd2
  have rd3 := poolManagerBlocks.poolManager_block_4778 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  have h320 : (free+⟨320⟩).toNat = free.toNat+320 := uadd_word_ofNat_toNat free 320 (by omega)
  have hobj := afterInitializeMemory_object mem free I.source key price tick (by omega)
  have hsize := hobj.inBounds
  rw [afterInitializePayload_size] at hsize
  obtain ⟨evm', z, out, hcall, henv, hworld, ho, hr⟩ := hookCallTrace v
    (by simp only [List.length_cons]; omega) hI hσ0 (by omega) hobj
    (by rw [afterInitializePayload_size]; decide)
    (by rw [afterInitializePayload_size]; decide) (by omega)
    (by rw [afterInitializePayload_size, h320]; omega) (by rw [h320]; omega)
    (afterInitializeMemory_free _ _ _ _ _ _)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
  refine ⟨evm', z, out, hcall, henv, hworld, ho, ?_⟩
  by_cases hh : z = true ∧ hookReplyValid (afterInitializePayload I.source key price tick) out
  · rw [if_pos hh] at hr ⊢
    obtain ⟨aw4, k4, C4, rd4⟩ := hr
    have rd5 := poolManagerBlocks.poolManager_block_4783 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
    have rd6 := poolManagerBlocks.poolManager_block_4605
      (by change R.length+5+3 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
    exact initializeReturnTrace v (by simp only [List.length_cons]; omega) rd6
  · rw [if_neg hh] at hr ⊢
    exact hr

end Benchmarks.UniswapV4PoolManager
