import Benchmarks.UniswapV4PoolManager.BeforeInitializeActiveTrace
import Benchmarks.UniswapV4PoolManager.HookWrapperSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeInitializeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256)
    (s0 evm evm' : State) (mem rdata : ByteArray) (free keyPtr price fee junk : UInt256)
    (key : PoolKeyWords) (hook : AccountAddress) (z : Bool) (out : ByteArray) (R : List UInt256) : Prop :=
  if hookEnabled I.source hook ⟨8192⟩ then
    if z = true ∧ hookReplyValid (beforeInitializePayload I.source key price) out then
      poolInitializeEntryTrace v I g s0 evm'
        (beforeInitializeReplyMemory mem free I.source key price out) out keyPtr price fee junk R
    else RDrev (deployedRuntime v) g s0
  else poolInitializeEntryTrace v I g s0 evm mem rdata keyPtr price fee junk R

theorem beforeInitializeHookTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free keyPtr price fee junk : UInt256}
    {key : PoolKeyWords} {hook : AccountAddress} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024)
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key) (hw : accountWord hook = key.hooks)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+291 ≤ solcMaxU64)
    (hgas : g.toNat < 324518553658429321982441292826060)
    (haw : aw.toNat ≤ 2048) (hs : free.toNat ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (h : RD (deployedRuntime v) I g s0 ⟨4257⟩
      (fee :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) :: keyPtr :: price ::
        (keyPtr+⟨96⟩) :: price :: junk :: R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ evm' z out,
      (hookEnabled I.source hook ⟨8192⟩ →
        callViaEVM evm hook 0 (beforeInitializePayload I.source key price) (z, evm', out)) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧ out.size < 2^138 ∧
      (z = true → out.size+4096 ≤ solcMaxU64) ∧
      beforeInitializeTraceResult v I g s0 evm evm' mem rdata free keyPtr price fee junk key hook z out R := by
  have hload : memLoad (keyPtr+⟨128⟩) mem = accountWord hook :=
    (hv.load (i := 4) (word := key.hooks) rfl).trans hw.symm
  have haw1 : (M aw (keyPtr+⟨128⟩) ⟨32⟩).toNat ≤ 2048 := by
    apply memoryWords_le haw
    change (keyPtr+UInt256.ofNat 128).toNat+32 ≤ 32*2048
    rw [uadd_word_ofNat_toNat keyPtr 128 (by have := hv.fits; omega)]
    omega
  have hclean := solcAddrMask_clean (accountWord_canonical hook)
  have heq : I.source = hook ↔ accountWord I.source = accountWord hook := by
    simpa only [accountWord_address] using accountWord_eq_iff I.source (accountWord hook) (accountWord_canonical hook)
  have hcond : UInt256.sub (UInt256.ofNat I.source.val)
      (UInt256.land (memLoad (keyPtr+⟨128⟩) mem) solcAddrMask) = ⟨0⟩ ↔ I.source = hook := by
    rw [hload, hclean, u256_sub_eq_zero_iff_eq]
    exact heq.symm
  have hst : poolManagerBlocks.poolManager_block_4257_taken_stack (mem := mem)
      (x0 := fee) (x1 := keyPtr+⟨32⟩) (x2 := keyPtr+⟨64⟩) (x3 := keyPtr+⟨128⟩)
      (x4 := keyPtr) (x5 := price) (x6 := keyPtr+⟨96⟩) (x7 := price) (R := junk :: R) =
      (accountWord hook :: accountWord hook :: price :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) ::
        (keyPtr+⟨128⟩) :: keyPtr :: price :: (keyPtr+⟨96⟩) :: fee :: junk :: R) := by
    change memLoad (keyPtr+⟨128⟩) mem :: UInt256.land (memLoad (keyPtr+⟨128⟩) mem) solcAddrMask ::
      price :: (keyPtr+⟨32⟩) :: (keyPtr+⟨64⟩) :: (keyPtr+⟨128⟩) :: keyPtr :: price ::
      (keyPtr+⟨96⟩) :: fee :: junk :: R = _
    rw [hload, hclean]
  by_cases he : I.source = hook
  · have hn : ¬hookEnabled I.source hook ⟨8192⟩ := fun hh => hh.1 he
    have rd1 := poolManagerBlocks.poolManager_block_4257_fallthrough
      (by simp only [List.length_cons]; omega) (hcond.mpr he) h
    have hst' : poolManagerBlocks.poolManager_block_4257_fallthrough_stack (mem := mem)
        (x0 := fee) (x1 := keyPtr+⟨32⟩) (x2 := keyPtr+⟨64⟩) (x3 := keyPtr+⟨128⟩)
        (x4 := keyPtr) (x5 := price) (x6 := keyPtr+⟨96⟩) (x7 := price) (R := junk :: R) = _ := hst
    rw [hst'] at rd1
    refine Or.inr ⟨evm, false, .empty, (fun hh => (hn hh).elim), hI, hσ0, by decide, (by simp), ?_⟩
    simp only [beforeInitializeTraceResult, if_neg hn]
    exact ⟨_, _, _, _, _, rd1⟩
  · have rd1 := poolManagerBlocks.poolManager_block_4257_taken
      (by simp only [List.length_cons]; omega) (fun hh => he (hcond.mp hh))
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    rw [hst] at rd1
    have hcomm : UInt256.land (UInt256.ofNat 8192) (accountWord hook) =
        UInt256.land (accountWord hook) ⟨8192⟩ := u256_land_comm _ _
    by_cases hz : UInt256.land (accountWord hook) ⟨8192⟩ = ⟨0⟩
    · have hn : ¬hookEnabled I.source hook ⟨8192⟩ := fun hh => hh.2 hz
      have rd2 := poolManagerBlocks.poolManager_block_4832_fallthrough
        (by simp only [List.length_cons]; omega) (hcomm.trans hz) rd1
      have rd3 := poolManagerBlocks.poolManager_block_4841
        (by change R.length+9+3 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      refine Or.inr ⟨evm, false, .empty, (fun hh => (hn hh).elim), hI, hσ0, by decide, (by simp), ?_⟩
      simp only [beforeInitializeTraceResult, if_neg hn]
      exact ⟨_, _, _, _, _, rd3⟩
    · have hen : hookEnabled I.source hook ⟨8192⟩ := ⟨he, hz⟩
      have rd2 := poolManagerBlocks.poolManager_block_4832_taken
        (by simp only [List.length_cons]; omega) (fun hh => hz (hcomm.symm.trans hh))
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      rcases beforeInitializeActiveTrace v hstack hI hσ0 hv hc hb hf hgas haw1 hs hfree rd2 with
        hog | ⟨evm', z, out, hcall, henv, hworld, ho, hbound, hr⟩
      · exact .inl hog
      · refine Or.inr ⟨evm', z, out, (fun _ => hcall), henv, hworld, ho, hbound, ?_⟩
        simpa only [beforeInitializeTraceResult, if_pos hen] using hr

end Benchmarks.UniswapV4PoolManager
