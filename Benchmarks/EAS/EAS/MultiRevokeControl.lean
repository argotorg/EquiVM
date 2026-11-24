import Benchmarks.EAS.EAS.MultiRequestControl
import Benchmarks.EAS.EAS.MultiRevocationDecode
import Benchmarks.EAS.EAS.CalldataSignedStride
import Benchmarks.EAS.EAS.MultiAttestControl
import Benchmarks.EAS.EAS.RuntimeBlocks_014

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revocationArrayAccessValid (cd : ByteArray) (root : UInt256) : Prop :=
  requestArrayReferenceValid cd root ∧
  (calldataWord cd (multiRequestArray cd root).toNat).toNat ≤ 2^64-1 ∧
  UInt256.sgt ((UInt256.ofNat 32)+multiRequestArray cd root)
    (UInt256.sub (UInt256.ofNat cd.size) (UInt256.shiftLeft (calldataWord cd (multiRequestArray cd root).toNat) (UInt256.ofNat 6))) = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) : Decidable (revocationArrayAccessValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem easRevocationArrayAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {root available : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+8 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3416⟩ (root::available::R) mem aw rdata σ k C) :
    (revocationArrayAccessValid ee.calldata root → ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨3503⟩
      (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat::
        available::root::(multiRequestArray ee.calldata root+UInt256.ofNat 32)::R) mem aw' rdata σ k' C') ∧
    (¬revocationArrayAccessValid ee.calldata root → RDrev fork (deployedRuntime v) g s0) := by
  have hneg : (UInt256.sub (UInt256.ofNat ee.calldata.size) root)+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639905 =
      (UInt256.ofNat ee.calldata.size-root)-⟨31⟩ := by rw [word_sub_eq_add_neg (UInt256.ofNat ee.calldata.size-root) ⟨31⟩]; rfl
  by_cases href : requestArrayReferenceValid ee.calldata root
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3416_fallthrough_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [hneg]; exact href) rd
    by_cases hlen : (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat).toNat ≤ 2^64-1
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_3466_fallthrough_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) (ugt_zero hlen) r1
      by_cases he : UInt256.sgt ((UInt256.ofNat 32)+multiRequestArray ee.calldata root)
          (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.shiftLeft (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat) (UInt256.ofNat 6))) = ⟨0⟩
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3487_fallthrough_packed (immWords := wordsOf (immStore v))
          (by omega) he r2
        refine ⟨fun _ => ⟨a3,k3,C3,?_⟩,fun h => (h ⟨href,hlen,he⟩).elim⟩
        simpa only [easBlocks.eas_block_3487_fallthrough_stack,
          easBlocks.eas_block_3466_fallthrough_stack,easBlocks.eas_block_3416_fallthrough_stack,
          multiRequestArray,u256_add_comm (UInt256.ofNat 32)] using r3
      · obtain ⟨a3,k3,C3,r3⟩ := easBlocks.eas_block_3487_taken_packed (immWords := wordsOf (immStore v))
          (by omega) he (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r2
        exact ⟨fun h => (he h.2.2).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
          (by simp only [easBlocks.eas_block_3487_taken_stack,List.length_cons]; omega) r3⟩
    · obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_3466_taken_packed (immWords := wordsOf (immStore v))
        (by first | omega | (simp only [List.length_cons]; omega)) (by rw [ugt_one (by change 18446744073709551615 < (calldataWord ee.calldata (multiRequestArray ee.calldata root).toNat).toNat; omega)]; decide)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨fun h => (hlen h.2.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
        (by simp only [easBlocks.eas_block_3466_taken_stack,List.length_cons]; omega) r2⟩
  · obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3416_taken_packed (immWords := wordsOf (immStore v))
      (by first | omega | (simp only [List.length_cons]; omega)) (by rw [hneg]; exact href)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨fun h => (href h.1).elim,fun _ => easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
      (by simp only [easBlocks.eas_block_3416_taken_stack,List.length_cons]; omega) r1⟩

theorem revocationArrayAccessValid_of_decode {cd : ByteArray} {root : UInt256} {rs : List RevocationRequestRecord}
    (hsize : cd.size < 2^255) (hd : decodeMultiRevocationAt cd root = some rs) : revocationArrayAccessValid cd root := by
  unfold decodeMultiRevocationAt at hd
  by_cases hr : requestArrayReferenceValid cd root
  · rw [if_pos hr] at hd
    have hh := (decodeRevocationArray_facts (by omega) hd).1
    refine ⟨hr,hh.1,?_⟩
    have hshift := wordShiftLeft_nat (calldataWord cd (multiRequestArray cd root).toNat) 6 (by decide)
    rw [hshift]
    apply calldataArrayExtent_signed_stride hsize (by have := hh.1; omega)
    simpa only [hshift] using hh.2
  · rw [if_neg hr] at hd
    contradiction

def multiRevokeLoopStack (n i : Nat) (base available : UInt256) (R : List UInt256) : List UInt256 :=
  available::UInt256.ofNat n::UInt256.ofNat i::base::(UInt256.ofNat n-⟨1⟩)::R
def multiRevokeSaved (n i : Nat) (base available : UInt256) (R : List UInt256) : List UInt256 :=
  ⟨1710⟩::available::⟨3537⟩::⟨1⟩::UInt256.ofNat n::UInt256.ofNat i::base::(UInt256.ofNat n-⟨1⟩)::R
def multiRevokeCopySaved (ee : ExecutionEnv) (n i : Nat) (base available : UInt256) (R : List UInt256) : List UInt256 :=
  multiRequestRoot ee.calldata base i::UInt256.ofNat ee.source.val::available::multiAttestLastWord n i::multiRevokeSaved n i base available R

theorem easMultiRevokeAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base available : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+20 ≤ 1024)
    (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3396⟩ (multiRevokeLoopStack n i base available R) mem aw rdata σ k C) :
    if multiRequestReferenceValid ee.calldata base i ∧ revocationArrayAccessValid ee.calldata (multiRequestRoot ee.calldata base i) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5924⟩
        ((multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)+UInt256.ofNat 32)::
          calldataWord ee.calldata (multiRequestArray ee.calldata (multiRequestRoot ee.calldata base i)).toNat::
          UInt256.ofNat ee.calldata.size::⟨3530⟩::multiRevokeCopySaved ee n i base available R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hin : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3396_taken_packed (immWords := wordsOf (immStore v))
    (by first | omega | (simp only [List.length_cons]; omega))
    (by rw [ult_one (by rw [hin,ulit_toNat' _ hn]; exact hi)]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_3405_packed (immWords := wordsOf (immStore v))
    (by first | omega | (simp only [List.length_cons]; omega)) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  have hindex := easMultiRequestIndex v (by simp only [easBlocks.eas_block_3405_stack,List.length_cons]; omega)
    hi hn hb (by rw [easPatchedValidJumps v]; jump_dest) r2
  by_cases href : multiRequestReferenceValid ee.calldata base i
  · rw [if_pos href] at hindex
    obtain ⟨a3,k3,C3,r3⟩ := hindex
    have ha := easRevocationArrayAccess v (by first | omega | (simp only [List.length_cons]; omega)) r3
    by_cases harr : revocationArrayAccessValid ee.calldata (multiRequestRoot ee.calldata base i)
    · rw [if_pos ⟨href,harr⟩]
      obtain ⟨a4,k4,C4,r4⟩ := ha.1 harr
      obtain ⟨a5,k5,C5,r5⟩ := easBlocks.eas_block_3503_packed (immWords := wordsOf (immStore v))
        (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r4
      exact ⟨a5,k5,C5,r5⟩
    · rw [if_neg (fun h => harr h.2)]
      exact ha.2 harr
  · rw [if_neg (fun h => href h.1)]
    simpa only [if_neg href] using hindex

theorem easMultiRevokeDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n : Nat}
    {base available : UInt256} {R : List UInt256} (v : EASImmutables) (hstack : R.length+7 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3396⟩ (multiRevokeLoopStack n n base available R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ ByteArray.empty := by
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3396_fallthrough_packed (immWords := wordsOf (immStore v))
    (by first | omega | (simp only [List.length_cons]; omega)) (ult_zero (le_refl _)) rd
  exact easBlocks.eas_block_3404 (immWords := wordsOf (immStore v)) (by first | omega | (simp only [List.length_cons]; omega)) r1

end Benchmarks.EAS.EAS
