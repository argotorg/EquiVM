import Benchmarks.Morpho.MetaMorphoV1_1.DomainSource
import Benchmarks.Morpho.MetaMorphoV1_1.DomainHashRoutines

/-! Short-circuit cache checks and the shared domain-separator bytecode routine. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem domainCachedThisCheck (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) :
    UInt256.eq (UInt256.land solcAddrMask (wordsOf (immStore v) "_cachedThis"))
      (UInt256.ofNat I.codeOwner.val) =
      if I.codeOwner = v._cachedThis then ⟨1⟩ else ⟨0⟩ := by
  rw [wordsOf_immStore__cachedThis]
  change UInt256.eq (UInt256.land solcAddrMask (UInt256.ofNat v._cachedThis.val))
    (UInt256.ofNat I.codeOwner.val) = _
  rw [solcAddrMask_clean_left (by
    rw [UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le v._cachedThis.isLt (by decide))]
    exact v._cachedThis.isLt)]
  by_cases h : I.codeOwner = v._cachedThis
  · rw [h, if_pos rfl, u256_eq_refl]
  · rw [if_neg h, u256_eq_of_ne]
    intro he
    have ha := congrArg (fun w : UInt256 ↦ AccountAddress.ofNat w.toNat) he
    change AccountAddress.ofNat (EVM.word v._cachedThis.val).toNat =
      AccountAddress.ofNat (EVM.word I.codeOwner.val).toNat at ha
    rw [accountAddress_of_word_val, accountAddress_of_word_val] at ha
    exact h ha.symm

theorem domainCacheGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨12937⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12987⟩
      ((if domainCacheValid v I then ⟨1⟩ else ⟨0⟩) :: R) mem aw rdata σ k' C' := by
  have hc := domainCachedThisCheck v I
  by_cases hthis : I.codeOwner = v._cachedThis
  · have h1 := metaMorphoV1_1_block_12937_taken (immWords := wordsOf (immStore v))
      hstack (by
        change UInt256.eq (UInt256.land solcAddrMask _) _ ≠ ⟨0⟩
        rw [hc, if_pos hthis]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    have h2 := metaMorphoV1_1_block_13180 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    refine ⟨k + 13 + 7, C + 43 + 22, ?_⟩
    simp only [metaMorphoV1_1_block_13180_stack, wordsOf_immStore__cachedChainId,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at h2
    by_cases hchain : UInt256.ofNat Ethereum.chainId = v._cachedChainId
    · simpa only [domainCacheValid, hthis, hchain, and_self, if_true, u256_eq_refl] using h2
    · simpa only [domainCacheValid, hthis, hchain, and_false, if_false,
        u256_eq_of_ne hchain] using h2
  · have h1 := metaMorphoV1_1_block_12937_fallthrough
      (immWords := wordsOf (immStore v)) hstack (by
        change UInt256.eq (UInt256.land solcAddrMask _) _ = ⟨0⟩
        rw [hc, if_neg hthis]) rd
    refine ⟨k + 13, C + 43, ?_⟩
    change RD _ _ _ _ _
      (UInt256.eq (UInt256.land solcAddrMask (wordsOf (immStore v) "_cachedThis"))
        (UInt256.ofNat I.codeOwner.val) :: R) _ _ _ _ _ _ at h1
    simpa only [hc, domainCacheValid, hthis, false_and, if_false] using h1

def domainSeparatorMemory (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv)
    (mem : ByteArray) (free : Nat) : ByteArray :=
  if domainCacheValid v I then mem else domainHashMemory v I mem free

theorem domainSeparatorRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 9 ≤ 1024)
    (hlo : 96 ≤ free) (hfit : free + 192 < 2 ^ 64)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12937⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (domainSeparatorWord v I :: R)
      (domainSeparatorMemory v I mem free) aw' rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := domainCacheGuard v (by simp only [List.length_cons]; omega) rd
  by_cases hvalid : domainCacheValid v I
  · simp only [if_pos hvalid] at h1
    have h2 := metaMorphoV1_1_block_12987_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by decide) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_12993_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h2
    refine ⟨aw3, k3, C3, ?_⟩
    simpa only [domainSeparatorWord, domainSeparatorMemory, if_pos hvalid,
      metaMorphoV1_1_block_12993_stack, wordsOf_immStore__cachedDomainSeparator,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] using h3
  · simp only [if_neg hvalid] at h1
    have h2 := metaMorphoV1_1_block_12987_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    simpa only [domainSeparatorWord, domainSeparatorMemory, if_neg hvalid] using
      domainHashRoutine v free hstack hlo hfit hfree hret h2

end Benchmarks.Morpho.MetaMorphoV1_1
