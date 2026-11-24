import Benchmarks.EAS.EAS.CalldataGuards
import Benchmarks.EAS.EAS.RequestDecode
import Benchmarks.EAS.EAS.RuntimeBlocks_025

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a direct calldata tail's signed bound, including wrapping pointers.
theorem solcTailTarget_reference (cd : ByteArray) (base head need : UInt256) (ty : ABIType)
    (ht : tailSize? ty = some need.toNat) :
    solcTailTarget? true ty cd.toList base.toNat head.toNat =
      if UInt256.isZero (UInt256.slt (calldataWord cd head.toNat)
          (UInt256.sub (UInt256.ofNat cd.size-base) (need-⟨1⟩))) = ⟨0⟩ then
        some (base+calldataWord cd head.toNat).toNat
      else none := by
  have hl : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hsub : solcSub cd.size base.toNat = (UInt256.ofNat cd.size-base).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
  have hs1 : solcSub need.toNat 1 = (need-⟨1⟩).toNat := solcSub_word need ⟨1⟩
  simp only [solcTailTarget?,solcReadNat_word_total,Bool.true_eq,if_true,ht,
    bind,pure,Option.bind_some,hl,hsub,hs1,solcSub_word,solcAdd_word]
  by_cases h : UInt256.isZero (UInt256.slt (calldataWord cd head.toNat)
      (UInt256.sub (UInt256.ofNat cd.size-base) (need-⟨1⟩))) = ⟨0⟩
  · rw [if_pos h,(solcSLT_word_true _ _).mpr h]
    rfl
  · have hs : solcSLT (calldataWord cd head.toNat).toNat (UInt256.sub (UInt256.ofNat cd.size-base) (need-⟨1⟩)).toNat = false := by
      cases he : solcSLT (calldataWord cd head.toNat).toNat (UInt256.sub (UInt256.ofNat cd.size-base) (need-⟨1⟩)).toNat
      · rfl
      · exact False.elim (h ((solcSLT_word_true _ _).mp he))
    rw [if_neg h,hs]
    rfl

-- LIBRARY CANDIDATE: word subtraction is addition of the modular negative.
theorem word_sub_eq_add_neg (a b : UInt256) : a-b = a+⟨-b.val⟩ := by
  apply u256_inj
  change (a.val-b.val).val = (a.val + -b.val).val
  rw [sub_eq_add_neg]

def requestReferenceValid (cd : ByteArray) (base head : UInt256) : Prop :=
  UInt256.isZero (UInt256.slt (calldataWord cd head.toNat)
    ((UInt256.ofNat cd.size-base)-⟨191⟩)) = ⟨0⟩
instance (cd : ByteArray) (base head : UInt256) : Decidable (requestReferenceValid cd base head) := by
  unfold requestReferenceValid; infer_instance

theorem requestReference_decode (cd : ByteArray) (base head : UInt256) :
    solcTailTarget? true requestDataABI cd.toList base.toNat head.toNat =
      if requestReferenceValid cd base head then some (base+calldataWord cd head.toNat).toNat else none := by
  exact solcTailTarget_reference cd base head ⟨192⟩ requestDataABI (by native_decide)

theorem easRequestReference {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {base head ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6189⟩ (base::head::ret::R) mem aw rdata σ k C) :
    if requestReferenceValid ee.calldata base head then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
        ((base+calldataWord ee.calldata head.toNat)::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hb : (UInt256.sub (UInt256.ofNat ee.calldata.size) base)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639745 =
      (UInt256.ofNat ee.calldata.size-base)-⟨191⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-base) ⟨191⟩]; rfl
  by_cases hv : requestReferenceValid ee.calldata base head
  · rw [if_pos hv]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6189_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hb]; exact hv) rd
    simp only [easBlocks.eas_block_6189_fallthrough_stack] at r1
    exact easBlocks.eas_block_6237_packed (immWords := wordsOf (immStore v)) (by omega) hret r1
  · rw [if_neg hv]
    obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_6189_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hb]; exact hv)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_6189_taken_stack,List.length_cons]; omega) r1

end Benchmarks.EAS.EAS
