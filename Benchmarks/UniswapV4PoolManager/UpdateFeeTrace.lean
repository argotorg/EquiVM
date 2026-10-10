import Benchmarks.UniswapV4PoolManager.UpdateFeeSource
import Benchmarks.UniswapV4PoolManager.PoolLPFeeTrace
import Benchmarks.UniswapV4PoolManager.LPFeeTrace
import Benchmarks.UniswapV4PoolManager.TransientTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_024

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem updateFeeAuthorizationTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw fee : UInt256} {key : PoolKeyWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+6 ≤ 1024) (hc : PoolKeyCanonical key)
    (h : RD (deployedRuntime v) I g s0 ⟨8594⟩ (fee :: ⟨160⟩ :: R) (poolKeyMemory key) aw rdata σ k C) :
    (¬dynamicFeeAuthorized I key ∧ RDrev (deployedRuntime v) g s0) ∨
    (dynamicFeeAuthorized I key ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8623⟩
      (⟨160⟩ :: fee :: R) (poolKeyMemory key) aw' rdata σ k' C') := by
  have hfee : UInt256.land (memLoad ((⟨160⟩ : UInt256) + UInt256.ofNat 64) (poolKeyMemory key))
      (UInt256.ofNat 16777215) = key.fee := by
    rw [show (⟨160⟩ : UInt256)+UInt256.ofNat 64 = UInt256.ofNat (160+32*2) from rfl,
      poolKeyMemory_load key (i := 2) rfl]
    exact u256LandMaskCleanOfToNat _ _ rfl hc.2.2.1
  have hhook : UInt256.land (memLoad ((⟨160⟩ : UInt256) + UInt256.ofNat 128) (poolKeyMemory key))
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = key.hooks := by
    rw [show (⟨160⟩ : UInt256)+UInt256.ofNat 128 = UInt256.ofNat (160+32*4) from rfl,
      poolKeyMemory_load key (i := 4) rfl]
    exact solcAddrMask_clean hc.2.2.2.2
  by_cases hd : key.fee.toNat = 8388608
  · have heq : key.fee = UInt256.ofNat 8388608 := u256_inj hd
    have rd1 := poolManagerBlocks.poolManager_block_8594_taken hstack
      (by rw [hfee, heq, uInt256_eq_self]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_8774 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    change RD _ _ _ _ ⟨8618⟩
      (UInt256.isZero (UInt256.eq (accountWord I.source)
        (UInt256.land (memLoad ((⟨160⟩ : UInt256)+UInt256.ofNat 128) (poolKeyMemory key))
          (UInt256.ofNat 1461501637330902918203684832716283019655932542975))) :: ⟨160⟩ :: fee :: R)
      (poolKeyMemory key) _ _ _ _ _ at rd2
    rw [hhook] at rd2
    by_cases hh : I.source = AccountAddress.ofNat key.hooks.toNat
    · have he : accountWord I.source = key.hooks := (accountWord_eq_iff _ _ hc.2.2.2.2).1 hh
      have rd3 := poolManagerBlocks.poolManager_block_8618_fallthrough (by simp; omega)
        (by rw [he, uInt256_eq_self]; decide) rd2
      exact .inr ⟨⟨hd, hh⟩, _, _, _, rd3⟩
    · have he : accountWord I.source ≠ key.hooks := fun he => hh ((accountWord_eq_iff _ _ hc.2.2.2.2).2 he)
      have hz : UInt256.eq (accountWord I.source) key.hooks = ⟨0⟩ :=
        uInt256_eq_zero_of_ne (fun h => he (uInt256_eq_one_eq h))
      have rd3 := poolManagerBlocks.poolManager_block_8618_taken (by simp; omega)
        (by rw [hz]; decide) (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact .inl ⟨fun ha => hh ha.2, poolManagerBlocks.poolManager_block_8734 (by change R.length+4 ≤ 1024; omega) rd3⟩
  · have heq : key.fee ≠ UInt256.ofNat 8388608 := fun he => hd (congrArg UInt256.toNat he)
    have hz : UInt256.eq key.fee (UInt256.ofNat 8388608) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h => heq (uInt256_eq_one_eq h))
    have rd1 := poolManagerBlocks.poolManager_block_8594_fallthrough hstack (by rw [hfee]; exact hz) h
    have rd2 := poolManagerBlocks.poolManager_block_8618_taken (by simp; omega)
      (by change UInt256.isZero (UInt256.eq _ _) ≠ ⟨0⟩; rw [hfee, hz]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact .inl ⟨fun ha => hd ha.1, poolManagerBlocks.poolManager_block_8734 (by change R.length+4 ≤ 1024; omega) rd2⟩

theorem updateFeePoolHashTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw fee : UInt256} {key : PoolKeyWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨8634⟩ (⟨160⟩ :: ⟨160⟩ :: fee :: R) (poolKeyMemory key) aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13686⟩
      (poolSlot (poolKeyId key) :: ⟨8656⟩ :: fee :: poolSlot (poolKeyId key) :: R)
      (twoWordHashMem (poolKeyId key) ⟨6⟩ (poolKeyMemory key)) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', rd⟩ := poolManagerBlocks.poolManager_block_8634_packed hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  let mem := twoWordHashMem (keccakWord ⟨160⟩ ⟨160⟩ (poolKeyMemory key)) ⟨6⟩ (poolKeyMemory key)
  change RD _ _ _ _ ⟨13686⟩
    (keccakWord ⟨0⟩ ⟨64⟩ mem :: ⟨8656⟩ :: fee :: keccakWord ⟨0⟩ ⟨64⟩ mem :: R)
    mem aw' rdata σ k' C' at rd
  dsimp only [mem] at rd
  rw [poolKeyMemory_hash, mappingMemory_slot_any] at rd
  exact ⟨_, _, _, rd⟩

@[irreducible] def updateFeeTraceResult (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (evm : EVM.State) (key : PoolKeyWords) (fee : UInt256) : Prop :=
  if dynamicFeeAuthorized I key then
    if fee.toNat ≤ 1000000 then poolSetFeeTraceResult v I g s0 evm (poolKeyId key) fee
    else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem updateFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {evm : EVM.State}
    {rdata : ByteArray} {aw fee : UInt256} {key : PoolKeyWords} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+7 ≤ 1024) (hI : evm.executionEnv = I)
    (hc : PoolKeyCanonical key) (hfee : fee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨8594⟩ (fee :: ⟨160⟩ :: R) (poolKeyMemory key) aw rdata evm.accountMap k C) :
    updateFeeTraceResult v I g s0 evm key fee := by
  unfold updateFeeTraceResult
  rcases updateFeeAuthorizationTrace v (by omega) hc h with ⟨ha, hr⟩ | ⟨ha, aw1, k1, C1, rd1⟩
  · rw [if_neg ha]; exact hr
  · rw [if_pos ha]
    have rd2 := poolManagerBlocks.poolManager_block_8623 (by simp; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hval := lpFeeValidateTrace v (by change R.length+7 ≤ 1024; exact hstack) hfee
      (by rw [deployedRuntime_jumps]; jump_dest) rd2
    by_cases hv : fee.toNat ≤ 1000000
    · rw [if_pos hv] at hval ⊢
      obtain ⟨k3, C3, rd3⟩ := hval
      obtain ⟨aw4, k4, C4, rd4⟩ := updateFeePoolHashTrace v (by omega) rd3
      exact poolLPFeeTrace v (by omega) hI hfee rd4
    · rw [if_neg hv] at hval ⊢; exact hval

end Benchmarks.UniswapV4PoolManager
