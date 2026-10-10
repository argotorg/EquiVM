import Benchmarks.Morpho.MetaMorphoV1_1.FallbackStringSetup

/-! The generic storage-string copy routine used by both domain fallbacks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem fallbackStringCopyReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (free : Nat) (hstack : R.length + 11 ≤ 1024)
    (hfree : free < 2 ^ 64)
    (hvalid : storageStringValid (codeOwnerStorageWord I σ base))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11857⟩
      (base :: UInt256.ofNat free :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (UInt256.ofNat (free + 32 +
        32 * stringWordCount (storageStringLength (codeOwnerStorageWord I σ base))) :: R)
      (fallbackStringMemory I σ mem base (codeOwnerStorageWord I σ base) free)
      aw' rdata σ k' C' := by
  let header := codeOwnerStorageWord I σ base
  let len := storageStringLength header
  have hlen : len.toNat < 2 ^ 255 := storageStringLength_lt _
  have hf : free < UInt256.size := lt_trans hfree (by decide)
  have hptr : (UInt256.ofNat free).toNat = free := UInt256.toNat_ofNat_of_lt hf
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachDecoder v (by omega) rd
  obtain ⟨aw2, k2, C2, h2⟩ := storageStringDecoderReturn v
    (by simp only [List.length_cons]; omega) hvalid
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  by_cases hflag : UInt256.land header ⟨1⟩ = ⟨0⟩
  · exact fallbackStringShortReturn v free (by omega)
      (by change free + 64 < 2 ^ 256; omega) hvalid hflag hret h2
  · obtain ⟨aw3, k3, C3, h3⟩ := fallbackStringLongStart v (by omega) hflag h2
    have hfit : (UInt256.ofNat free).toNat + 0 + 32 * stringWordCount len + 32 <
        UInt256.size := by
      rw [hptr]
      change free + 0 + 32 * ((len.toNat + 31) / 32) + 32 < 2 ^ 256
      omega
    obtain ⟨aw4, k4, C4, h4⟩ := storageStringCopyLoop (len := len) v .fallback
      (stringWordCount len) 0 (by simp only [List.length_cons]; omega)
      (by unfold stringWordCount; omega)
      (by intro i hi; unfold stringWordCount at hi; omega) hfit h3
    obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_11922_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h4
    have hend : (UInt256.ofNat free + UInt256.ofNat (0 + 32 * stringWordCount len)) +
        UInt256.ofNat 32 = UInt256.ofNat (free + 32 + 32 * stringWordCount len) := by
      rw [ofNat_add_words, ofNat_add_words]
      congr 1
      omega
    refine ⟨aw5, k5, C5, ?_⟩
    simp only [header] at hflag
    simpa only [metaMorphoV1_1_block_11922_stack, hend, hptr, Nat.add_zero,
      fallbackStringMemory, if_neg hflag] using h5

theorem fallbackStringCopyRevertsHeader {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbad : ¬ storageStringValid (codeOwnerStorageWord I σ base))
    (rd : RD (deployedRuntime v) I g s0 ⟨11857⟩
      (base :: ptr :: ret :: R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := fallbackStringReachDecoder v (by omega) rd
  exact storageStringDecoderRevert v (by simp only [List.length_cons]; omega) hbad h1

end Benchmarks.Morpho.MetaMorphoV1_1
