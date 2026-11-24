import Benchmarks.EAS.EAS.BuildDomainEVM
import Benchmarks.EAS.EAS.DomainSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem domainAddressCheck (v : EASImmutables) (owner : AccountAddress) :
    UInt256.eq (UInt256.ofNat owner.val)
      (UInt256.land (wordsOf (immStore v) "_CACHED_THIS")
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) =
      (if owner = v._CACHED_THIS then UInt256.ofNat 1 else UInt256.ofNat 0) := by
  rw [wordsOf_immStore__CACHED_THIS]
  have hm := addressWord_val_clean v._CACHED_THIS
  change UInt256.land (UInt256.ofNat v._CACHED_THIS.val)
    (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat v._CACHED_THIS.val at hm
  change UInt256.eq (UInt256.ofNat owner.val)
    (UInt256.land (UInt256.ofNat v._CACHED_THIS.val)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = _
  rw [hm]
  by_cases h : owner = v._CACHED_THIS
  · rw [if_pos h, h, uInt256_eq_self]
    rfl
  · rw [if_neg h]
    have hn : UInt256.ofNat owner.val ≠ UInt256.ofNat v._CACHED_THIS.val := by
      intro he
      apply h
      apply Fin.ext
      have he' := congrArg UInt256.toNat he
      simpa only [show (UInt256.ofNat owner.val).toNat = owner.val from addressWord_toNat_val owner,
        show (UInt256.ofNat v._CACHED_THIS.val).toNat = v._CACHED_THIS.val from addressWord_toNat_val v._CACHED_THIS] using he'
    exact uInt256_eq_zero_of_ne (fun he => hn (uInt256_eq_one_eq he))

theorem domainChainCheck (v : EASImmutables) :
    UInt256.eq (UInt256.ofNat Ethereum.chainId) (wordsOf (immStore v) "_CACHED_CHAIN_ID") =
      (if Ethereum.chainId = v._CACHED_CHAIN_ID.toNat then UInt256.ofNat 1 else UInt256.ofNat 0) := by
  rw [wordsOf_immStore__CACHED_CHAIN_ID, wordOfInt_ofNat_toNat]
  by_cases h : Ethereum.chainId = v._CACHED_CHAIN_ID.toNat
  · rw [if_pos h, h, u256_ofNat_toNat, uInt256_eq_self]
    rfl
  · rw [if_neg h]
    have hn : UInt256.ofNat Ethereum.chainId ≠ v._CACHED_CHAIN_ID := by
      intro he
      apply h
      exact congrArg UInt256.toNat he
    exact uInt256_eq_zero_of_ne (fun he => hn (uInt256_eq_one_eq he))

theorem easDomain_dispatch {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 3 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13959⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0
      (if domainCacheHit v ee.codeOwner then ⟨14028⟩ else ⟨14063⟩) R mem aw rdata σ k' C' := by
  by_cases ha : ee.codeOwner = v._CACHED_THIS
  · have hc : UInt256.eq (UInt256.ofNat ee.codeOwner.val)
        (UInt256.land (wordsOf (immStore v) "_CACHED_THIS")
          (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = UInt256.ofNat 1 := by
      rw [domainAddressCheck, if_pos ha]
    have rd1 := easBlocks.eas_block_13959_taken (immWords := wordsOf (immStore v)) hstack
      (by rw [hc]; decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have rd2 := easBlocks.eas_block_14215 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [easBlocks.eas_block_14215_stack, domainChainCheck] at rd2
    by_cases hb : Ethereum.chainId = v._CACHED_CHAIN_ID.toNat
    · rw [if_pos hb] at rd2
      have rd3 := easBlocks.eas_block_14022_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by decide) rd2
      rw [if_pos (show domainCacheHit v ee.codeOwner from ⟨ha, hb⟩)]
      exact ⟨k + 9 + 7 + 4, C + 31 + 22 + 17, rd3⟩
    · rw [if_neg hb] at rd2
      have rd3 := easBlocks.eas_block_14022_taken (immWords := wordsOf (immStore v))
        (by omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
      rw [if_neg (show ¬ domainCacheHit v ee.codeOwner from fun h => hb h.2)]
      exact ⟨k + 9 + 7 + 4, C + 31 + 22 + 17, rd3⟩
  · have hc : UInt256.eq (UInt256.ofNat ee.codeOwner.val)
        (UInt256.land (wordsOf (immStore v) "_CACHED_THIS")
          (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) = UInt256.ofNat 0 := by
      rw [domainAddressCheck, if_neg ha]
    have rd1 := easBlocks.eas_block_13959_fallthrough (immWords := wordsOf (immStore v)) hstack hc rd
    simp only [easBlocks.eas_block_13959_fallthrough_stack, hc] at rd1
    have rd2 := easBlocks.eas_block_14022_taken (immWords := wordsOf (immStore v))
      (by omega) (by decide) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    rw [if_neg (show ¬ domainCacheHit v ee.codeOwner from fun h => ha h.1)]
    exact ⟨k + 9 + 4, C + 31 + 17, rd2⟩

def domainMemory (v : EASImmutables) (owner : AccountAddress) (mem : ByteArray) (heap : Nat) : ByteArray :=
  if domainCacheHit v owner then mem
  else buildDomainMemory mem heap v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION owner

theorem easDomain_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hlo : 96 ≤ heap.toNat)
    (hguard : domainCacheHit v ee.codeOwner ∨
      (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192))
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13959⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (domainWord v ee.codeOwner :: R)
      (domainMemory v ee.codeOwner mem heap.toNat) aw' rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := easDomain_dispatch v (by simp only [List.length_cons]; omega) rd
  by_cases hc : domainCacheHit v ee.codeOwner
  · rw [if_pos hc] at rd1
    have rd2 := easBlocks.eas_block_14028 (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
    refine ⟨aw, k1 + 3, C1 + 14, ?_⟩
    simpa only [easBlocks.eas_block_14028_stack, wordsOf_immStore__CACHED_DOMAIN_SEPARATOR,
      wordOfInt_ofNat_toNat, domainWord, domainMemory, if_pos hc] using rd2
  · rw [if_neg hc] at rd1
    have hg := hguard.resolve_left hc
    simpa only [domainWord, domainMemory, if_neg hc] using easBuildDomain_ok v hstack hfree hlo hg hvalid rd1

theorem easDomain_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hc : ¬ domainCacheHit v ee.codeOwner)
    (hguard : ¬ (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13959⟩ R mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, rd1⟩ := easDomain_dispatch v (by omega) rd
  rw [if_neg hc] at rd1
  exact easBuildDomain_revert v hstack hfree hguard rd1

end Benchmarks.EAS.EAS
