import Benchmarks.Morpho.MorphoBlue.ErrorMemory
import Benchmarks.Morpho.MorphoBlue.NarrowingSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def uint128ErrorMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 20)
    (UInt256.ofNat 49474313745504357941522707766437553544126227675921007535886519822381247102976) mem

section Narrowing
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {x ret : UInt256} {R : List UInt256}

theorem morphoToUint128Message (hstack : R.length + 16 ≤ 1024)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480) (x :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (UInt256.isZero (UInt256.gt x uint128Mask) :: memLoad (UInt256.ofNat 64) mem ::
        UInt256.ofNat 15565 :: x :: uint128Mask :: ret :: R)
      (uint128ErrorMem mem) aw' rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_15480 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoAlloc64 (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd1
  have rd3 := morphoBlocks.morpho_block_15493 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨_, _, _, rd3⟩

theorem morphoToUint128Ok (hstack : R.length + 16 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (hc : x.toNat < 2 ^ 128)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480) (x :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (x :: R)
      (uint128ErrorMem mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoToUint128Message (v := v) hstack hfit h
  have hg : UInt256.gt x uint128Mask = ⟨0⟩ := ugt_zero (by change x.toNat ≤ 2 ^ 128 - 1; omega)
  obtain ⟨k2, C2, rd2⟩ := morphoRequireTrue (v := v)
    (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hg]; decide) rd1
  have rd3 := morphoBlocks.morpho_block_15565 (immWords := wordsOf (immStore v))
    (by omega) hvalid rd2
  refine ⟨aw1, k2 + 4, C2 + 15, ?_⟩
  simpa only [morphoBlocks.morpho_block_15565_stack,
    show UInt256.land x uint128Mask = x from halfWord_low_clean x hc] using rd3

theorem morphoToUint128Reverts (hstack : R.length + 16 ≤ 1024)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (hsize : 96 ≤ mem.size) (hptr : 96 ≤ (memLoad (UInt256.ofNat 64) mem).toNat)
    (hgap : (memLoad (UInt256.ofNat 64) mem).toNat - mem.size < USize.size)
    (hhi : (memLoad (UInt256.ofNat 64) mem).toNat + 100 < UInt256.size)
    (hover : 2 ^ 128 ≤ x.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480) (x :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoToUint128Message (v := v) hstack hfit h
  have hg : UInt256.gt x uint128Mask = ⟨1⟩ := ugt_one (by change 2 ^ 128 - 1 < x.toNat; omega)
  have hlen : morphoErrorLength (uint128ErrorMem mem) (memLoad (UInt256.ofNat 64) mem) =
      UInt256.ofNat 20 := (morphoErrorMem_properties_general _ _ _ _ hptr rfl hsize hgap hhi).2.2
  exact morphoRequireFalseShort (v := v) (by simp only [List.length_cons]; omega)
    (by rw [hg]; decide) (by rw [hlen]; decide) (by rw [hlen]; decide) rd1

end Narrowing
end Benchmarks.Morpho.MorphoBlue
