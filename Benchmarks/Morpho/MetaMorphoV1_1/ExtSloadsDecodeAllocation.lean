import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeHeader

/-! Array allocation and payload bounds after the dynamic-return header has been read. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def extSloadsArraySize (out : ByteArray) : UInt256 :=
  UInt256.ofNat (32 + 32 * extSloadsReturnCount out)

def extSloadsArrayHeaderMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (writeWord mem 64 (nextCursor ptr (extSloadsArraySize out))) ptr.toNat
    (UInt256.ofNat (extSloadsReturnCount out))

set_option maxRecDepth 2000 in
theorem extSloadsDecodeAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C base : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbound : base + out.size ≤ 2 ^ 200)
    (hheader : extSloadsHeaderChecks out) (hptr : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨13272⟩
      (extSloadsArraySize out :: UInt256.ofNat (extSloadsReturnCount out) ::
        UInt256.ofNat (base + out.size) :: UInt256.ofNat (base + extSloadsReturnOffset out) :: R)
      mem aw out σ k C) :
    ((¬ extSloadsReturnChecks out ∨ ¬ allocationFits ptr (extSloadsArraySize out)) ∧
      RDrev (deployedRuntime v) g s0) ∨
      (extSloadsReturnChecks out ∧ allocationFits ptr (extSloadsArraySize out) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13309⟩
          (UInt256.ofNat (base + extSloadsReturnOffset out) :: (ptr + ⟨32⟩) ::
            UInt256.ofNat (base + extSloadsReturnOffset out + 32 * extSloadsReturnCount out + 32) ::
            ptr :: R) (extSloadsArrayHeaderMem mem ptr out) aw' out σ k' C') := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hptr
  have h1 := metaMorphoV1_1_block_13272 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_13272_stack, hptr] at h1
  by_cases hfit : allocationFits ptr (extSloadsArraySize out)
  · obtain ⟨aw1, k1, C1, h2⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by
        change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
          (wordsOf (immStore v))) 0).contains (UInt256.ofNat 13286) = true
        rw [metaMorphoV1_1PatchedValidJumpsRuntime v]
        jump_dest) h1
    have hoff := hheader.2.1
    have hcount := hheader.2.2.2
    change extSloadsReturnOffset out ≤ 18446744073709551615 at hoff
    change extSloadsReturnCount out ≤ 18446744073709551615 at hcount
    have hm : 32 * extSloadsReturnCount out < UInt256.size := by change _ < 2 ^ 256; omega
    have he : base + out.size < UInt256.size := by change _ < 2 ^ 256; omega
    have hd : base + extSloadsReturnOffset out + 32 * extSloadsReturnCount out + 32 <
        UInt256.size := by change _ < 2 ^ 256; omega
    have hshift : UInt256.shiftLeft (UInt256.ofNat (extSloadsReturnCount out))
        (UInt256.ofNat 5) = UInt256.ofNat (32 * extSloadsReturnCount out) :=
      shiftLeft5_ofNat_eq hm
    by_cases hdata : extSloadsReturnOffset out + 32 + 32 * extSloadsReturnCount out ≤ out.size
    · obtain ⟨aw2, k2, C2, h3⟩ := metaMorphoV1_1_block_13286_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [hshift, ofNat_add_words, ofNat_add_words]
            exact ugt_zero (by
              rw [UInt256.toNat_ofNat_of_lt hd, UInt256.toNat_ofNat_of_lt he]
              omega))
        h2
      refine .inr ⟨⟨hheader.1, hheader.2.1, hheader.2.2.1, hheader.2.2.2, hdata⟩,
        hfit, aw2, k2, C2, ?_⟩
      simpa only [metaMorphoV1_1_block_13286_fallthrough_stack,
        metaMorphoV1_1_block_13286_fallthrough_memory, hshift, ofNat_add_words,
        extSloadsArrayHeaderMem, Reasoning.Theory.writeWord] using h3
    · have h3 := metaMorphoV1_1_block_13286_taken
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [hshift, ofNat_add_words, ofNat_add_words, ugt_one (by
              rw [UInt256.toNat_ofNat_of_lt hd, UInt256.toNat_ofNat_of_lt he]; omega)]
            decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact .inl ⟨.inl (fun hc => hdata hc.data),
        metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
          (by simp only [metaMorphoV1_1_block_13286_taken_stack, List.length_cons]; omega) h3⟩
  · exact .inl ⟨.inr hfit,
      allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
