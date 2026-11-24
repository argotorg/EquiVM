import Benchmarks.EAS.EAS.MultiRequestDecode
import Benchmarks.EAS.EAS.RuntimeBlocks_020
import Benchmarks.EAS.EAS.RuntimeBlocks_021

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easMultiRequestIndex {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i n : Nat}
    {base ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hi : i<n) (hn : n < UInt256.size) (hb : base.toNat+32*i < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5196⟩
      (base::UInt256.ofNat n::UInt256.ofNat i::ret::R) mem aw rdata σ k C) :
    if multiRequestReferenceValid ee.calldata base i then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (multiRequestRoot ee.calldata base i::R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) = UInt256.ofNat (32*i) :=
    shiftLeft5_ofNat_eq (by omega)
  have hslot : (base+UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat = base.toNat+32*i := by
    rw [hshift,uadd_word_ofNat_toNat _ _ hb]
  have hneg : (UInt256.sub (UInt256.ofNat ee.calldata.size) base)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639873 =
      (UInt256.ofNat ee.calldata.size-base)-⟨63⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-base) ⟨63⟩]; rfl
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5196_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [ult_one (by rw [hin,ulit_toNat' _ hn]; exact hi)]; rfl) rd
  simp only [easBlocks.eas_block_5196_fallthrough_stack] at r1
  by_cases hv : multiRequestReferenceValid ee.calldata base i
  · rw [if_pos hv]
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5206_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hslot,hneg]; exact hv) r1
    obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5257_packed (immWords := wordsOf (immStore v)) (by omega) hret r2
    exact ⟨a3,k3,C3,by simpa only [easBlocks.eas_block_5257_stack,easBlocks.eas_block_5206_fallthrough_stack,
      hslot,multiRequestRoot] using r3⟩
  · rw [if_neg hv]
    obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5206_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hslot,hneg]; exact hv)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
    exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5206_taken_stack,List.length_cons]; omega) r2

def requestArrayAccessValid (cd : ByteArray) (root : UInt256) : Prop :=
  requestArrayReferenceValid cd root ∧
  (calldataWord cd (multiRequestArray cd root).toNat).toNat ≤ 2^64-1 ∧
  UInt256.sgt ((UInt256.ofNat 32)+multiRequestArray cd root)
    (UInt256.sub (UInt256.ofNat cd.size) (UInt256.shiftLeft (calldataWord cd (multiRequestArray cd root).toNat) (UInt256.ofNat 5))) = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) : Decidable (requestArrayAccessValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem easRequestArrayAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root ret : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+6 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5260⟩ (root::(root+UInt256.ofNat 32)::ret::R) mem aw rdata σ k C) :
    (requestArrayAccessValid ee.calldata root → ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat::
        (multiRequestArray ee.calldata root+UInt256.ofNat 32)::R) mem aw' rdata σ k' C') ∧
    (¬requestArrayAccessValid ee.calldata root → RDrev fork (deployedRuntime v) g s0) := by
  have hneg : (UInt256.sub (UInt256.ofNat ee.calldata.size) root)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905 =
      (UInt256.ofNat ee.calldata.size-root)-⟨31⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-root) ⟨31⟩]; rfl
  by_cases href : requestArrayReferenceValid ee.calldata root
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5260_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hneg]; exact href) rd
    by_cases hlen : (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat).toNat ≤ 2^64-1
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5308_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (ugt_zero hlen) r1
      by_cases he : UInt256.sgt ((UInt256.ofNat 32)+multiRequestArray ee.calldata root)
          (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat) (UInt256.ofNat 5))) = ⟨0⟩
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5327_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) he r2
        obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_5343_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hret r3
        refine ⟨fun _ => ⟨a4,k4,C4,?_⟩,fun h => (h ⟨href,hlen,he⟩).elim⟩
        simpa only [easBlocks.eas_block_5343_stack,easBlocks.eas_block_5327_fallthrough_stack,
          easBlocks.eas_block_5308_fallthrough_stack,easBlocks.eas_block_5260_fallthrough_stack,
          multiRequestArray,u256_add_comm (UInt256.ofNat 32)] using r4
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_5327_taken_packed (immWords := wordsOf (immStore v))
          (by omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
        exact ⟨fun h => (he h.2.2).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_5327_taken_stack,List.length_cons]; omega) r3⟩
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_5308_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [ugt_one (by change 18446744073709551615 < (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat).toNat; omega)]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨fun h => (hlen h.2.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_5308_taken_stack,List.length_cons]; omega) r2⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_5260_taken_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [hneg]; exact href)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨fun h => (href h.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_5260_taken_stack,List.length_cons]; omega) r1⟩

end Benchmarks.EAS.EAS
