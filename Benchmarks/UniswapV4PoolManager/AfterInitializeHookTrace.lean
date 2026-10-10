import Benchmarks.UniswapV4PoolManager.AfterInitializeActiveTrace
import Benchmarks.UniswapV4PoolManager.HookWrapperSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def afterInitializeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm evm' : State) (key : PoolKeyWords) (price tick : UInt256)
    (hook : AccountAddress) (z : Bool) (out : ByteArray) : Prop :=
  if hookEnabled I.source hook ⟨4096⟩ then
    if z = true ∧ hookReplyValid (afterInitializePayload I.source key price tick) out then
      RDret (deployedRuntime v) g s0 evm'.accountMap tick.toByteArray
    else RDrev (deployedRuntime v) g s0
  else RDret (deployedRuntime v) g s0 evm.accountMap tick.toByteArray

theorem afterInitializeHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr price tick junk : UInt256}
    {key : PoolKeyWords} {hook : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+323 ≤ solcMaxU64)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4555⟩
      (accountWord hook :: keyPtr :: price :: tick :: ⟨32⟩ :: junk :: R) mem aw rdata evm.accountMap k C) :
    ∃ evm' z out,
      (hookEnabled I.source hook ⟨4096⟩ →
        callViaEVM evm hook 0 (afterInitializePayload I.source key price tick) (z, evm', out)) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      afterInitializeTraceResult v I g s0 evm evm' key price tick hook z out := by
  have hclean := solcAddrMask_clean (accountWord_canonical hook)
  have hclean' : UInt256.land (accountWord hook)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = accountWord hook := hclean
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  have hcond : UInt256.sub (UInt256.ofNat I.source.val)
      (UInt256.land (accountWord hook) solcAddrMask) = ⟨0⟩ ↔ I.source = hook := by
    rw [hclean, u256_sub_eq_zero_iff_eq]
    exact heq.symm
  by_cases he : I.source = hook
  · have hn : ¬hookEnabled I.source hook ⟨4096⟩ := fun hh => hh.1 he
    have rd1 := poolManagerBlocks.poolManager_block_4555_fallthrough
      (by simp only [List.length_cons]; omega) (hcond.mpr he) h
    simp only [poolManagerBlocks.poolManager_block_4555_fallthrough_stack, hclean'] at rd1
    refine ⟨evm, false, .empty, (fun hh => (hn hh).elim), hI, hσ0, by decide, ?_⟩
    simp only [afterInitializeTraceResult, if_neg hn]
    exact initializeReturnTrace v (by simp only [List.length_cons]; omega) rd1
  · have rd1 := poolManagerBlocks.poolManager_block_4555_taken
      (by simp only [List.length_cons]; omega) (fun hh => he (hcond.mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_4555_taken_stack, hclean'] at rd1
    have hcomm : UInt256.land (UInt256.ofNat 4096) (accountWord hook) =
        UInt256.land (accountWord hook) ⟨4096⟩ := u256_land_comm _ _
    by_cases hz : UInt256.land (accountWord hook) ⟨4096⟩ = ⟨0⟩
    · have hn : ¬hookEnabled I.source hook ⟨4096⟩ := fun hh => hh.2 hz
      have rd2 := poolManagerBlocks.poolManager_block_4596_fallthrough
        (by simp only [List.length_cons]; omega) (hcomm.trans hz) rd1
      have rd3 := poolManagerBlocks.poolManager_block_4605
        (by change R.length+5+3 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine ⟨evm, false, .empty, (fun hh => (hn hh).elim), hI, hσ0, by decide, ?_⟩
      simp only [afterInitializeTraceResult, if_neg hn]
      exact initializeReturnTrace v (by simp only [List.length_cons]; omega) rd3
    · have hen : hookEnabled I.source hook ⟨4096⟩ := ⟨he, hz⟩
      have rd2 := poolManagerBlocks.poolManager_block_4596_taken
        (by simp only [List.length_cons]; omega) (fun hh => hz (hcomm.symm.trans hh))
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      obtain ⟨evm', z, out, hcall, henv, hworld, ho, hr⟩ :=
        afterInitializeActiveTrace v hstack hI hσ0 hv hc hb hf hfree rd2
      refine ⟨evm', z, out, (fun _ => hcall), henv, hworld, ho, ?_⟩
      simpa only [afterInitializeTraceResult, if_pos hen] using hr

end Benchmarks.UniswapV4PoolManager
