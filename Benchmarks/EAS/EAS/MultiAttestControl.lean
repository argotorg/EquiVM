import Benchmarks.EAS.EAS.MultiAttestHead
import Benchmarks.EAS.EAS.MultiRequestControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestSaved (n i : Nat) (base table available count : UInt256) (R : List UInt256) : List UInt256 :=
  ⟨3853⟩::⟨32⟩::count::⟨1⟩::UInt256.ofNat n::(UInt256.ofNat n-⟨1⟩)::available::base::table::UInt256.ofNat i::R
def multiAttestLastWord (n i : Nat) : UInt256 := UInt256.eq (UInt256.ofNat i) (UInt256.ofNat n-⟨1⟩)
def multiAttestCopySaved (ee : ExecutionEnv) (n i : Nat) (base table available count : UInt256) (R : List UInt256) : List UInt256 :=
  multiRequestRoot ee.calldata base i::UInt256.ofNat ee.source.val::available::multiAttestLastWord n i::⟨3131⟩::
    multiAttestSaved n i base table available count R

theorem easMultiAttestAccess {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base table available count : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+30 ≤ 1024) (hi : i<n) (hn : n<UInt256.size) (hb : base.toNat+32*i<UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3767⟩ (multiAttestLoopStack n i base table available count R) mem aw rdata σ k C) :
    let root := multiRequestRoot ee.calldata base i
    let header := multiRequestArray ee.calldata root
    if multiRequestReferenceValid ee.calldata base i ∧ requestArrayAccessValid ee.calldata root then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨5544⟩
        ((header+UInt256.ofNat 32)::calldataWord ee.calldata header.toNat::UInt256.ofNat ee.calldata.size::⟨3846⟩::
          multiAttestCopySaved ee n i base table available count R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  have hc : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) ≠ ⟨0⟩ := by
    rw [ult_one (by rw [ulit_toNat' _ (by omega : i<UInt256.size),ulit_toNat' _ hn]; exact hi)]
    decide
  obtain ⟨a1,k1,C1,r1⟩ := easBlocks.eas_block_3767_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨a2,k2,C2,r2⟩ := easBlocks.eas_block_3787_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [easBlocks.eas_block_3787_stack] at r2
  have hr := easMultiRequestIndex v (by simp only [List.length_cons]; omega) hi hn hb
    (by rw [easPatchedValidJumps v]; jump_dest) r2
  by_cases href : multiRequestReferenceValid ee.calldata base i
  · rw [if_pos href] at hr
    obtain ⟨a3,k3,C3,r3⟩ := hr
    obtain ⟨a4,k4,C4,r4⟩ := easBlocks.eas_block_3817_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r3
    simp only [easBlocks.eas_block_3817_stack] at r4
    have ha := easRequestArrayAccess v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) r4
    by_cases harray : requestArrayAccessValid ee.calldata (multiRequestRoot ee.calldata base i)
    · rw [if_pos ⟨href,harray⟩]
      obtain ⟨a5,k5,C5,r5⟩ := ha.1 harray
      obtain ⟨a6,k6,C6,r6⟩ := easBlocks.eas_block_3832_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) r5
      exact ⟨a6,k6,C6,by simpa only [easBlocks.eas_block_3832_stack,multiAttestCopySaved,multiAttestSaved,multiAttestLastWord] using r6⟩
    · rw [if_neg (fun h => harray h.2)]
      exact ha.2 harray
  · rw [if_neg (fun h => href h.1)]
    simpa only [if_neg href] using hr

theorem easMultiAttestCall {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {base table available count data : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+17 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3846⟩
      (data::multiAttestCopySaved ee n i base table available count R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨9856⟩
      (calldataWord ee.calldata (multiRequestRoot ee.calldata base i).toNat::data::UInt256.ofNat ee.source.val::available::
        multiAttestLastWord n i::⟨3131⟩::multiAttestSaved n i base table available count R) mem aw' rdata σ k' C' := by
  obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_3846_packed (immWords := wordsOf (immStore v))
    (by simp only [multiAttestSaved,List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨a,j,D,h⟩

theorem easMultiAttestDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n : Nat}
    {base table available count : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3767⟩ (multiAttestLoopStack n n base table available count R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨11975⟩
      (table::count::⟨2797⟩::⟨398⟩::multiAttestLoopStack n n base table available count R) mem aw' rdata σ k' C' := by
  obtain ⟨a1,j1,D1,h1⟩ := easBlocks.eas_block_3767_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
  obtain ⟨a2,j2,D2,h2⟩ := easBlocks.eas_block_3775_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) h1
  exact ⟨a2,j2,D2,h2⟩

end Benchmarks.EAS.EAS
