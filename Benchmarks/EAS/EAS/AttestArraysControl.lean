import Benchmarks.EAS.EAS.AttestArrayMemory
import Benchmarks.EAS.EAS.AttestLoopControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestArraysStartPC : UIDSite → UInt256
  | .single .. => ⟨7819⟩ | .many .. => ⟨10040⟩
def attestArraysStartStack (site : UIDSite) (schema : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single len s av ret data _ result attester => schema::len::s::attester::data::av::result::ret::R
  | .many av last ret s len _ => len::schema::av::last::ret::s::R

def attestRecordsReturnPC : UIDSite → UInt256
  | .single .. => ⟨7830⟩ | .many .. => ⟨10049⟩
def attestRecordsSaved (site : UIDSite) (schema : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single len s av ret data _ result attester => schema::data::s::len::attester::av::result::ret::R
  | .many av last ret s len _ => s::schema::av::last::ret::len::R

def attestValuesReturnPC : UIDSite → UInt256
  | .single .. => ⟨7840⟩ | .many .. => ⟨10059⟩
def attestValuesSaved (site : UIDSite) (schema records : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single len s av ret data _ result attester => len::schema::data::s::records::attester::av::result::ret::R
  | .many av last ret s len _ => s::records::schema::av::last::ret::len::R

theorem easAttestRecordsStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+11 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestArraysStartPC site) (attestArraysStartStack site schema R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7541⟩
      (attestLoopLength site::attestRecordsReturnPC site::attestRecordsSaved site schema R) mem aw' rdata σ k' C' := by
  have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7541) = true := by rw [easPatchedValidJumps v]; jump_dest
  cases site with
  | single len s av ret data values result attester =>
    exact easBlocks.eas_block_7819_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd rd
  | many av last ret s len data =>
    exact easBlocks.eas_block_10040_packed (immWords := wordsOf (immStore v)) (by omega) hd rd

theorem easAttestValuesStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema records : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+12 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestRecordsReturnPC site)
      (records::attestRecordsSaved site schema R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7240⟩
      (attestLoopLength site::attestValuesReturnPC site::attestValuesSaved site schema records R) mem aw' rdata σ k' C' := by
  have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7240) = true := by rw [easPatchedValidJumps v]; jump_dest
  cases site with
  | single len s av ret data values result attester =>
    exact easBlocks.eas_block_7830_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd rd
  | many av last ret s len data =>
    exact easBlocks.eas_block_10049_packed (immWords := wordsOf (immStore v)) (by omega) hd rd

theorem easAttestArraysDone {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema records values t3 t4 : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+12 ≤ 1024) (ha : recordArrayPtr site t3 t4 = records) (hv : recordValuesPtr site t4 = values)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestValuesReturnPC site)
      (values::attestValuesSaved site schema records R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site schema ⟨0⟩ t3 t4 R) mem aw' rdata σ k' C' := by
  cases site with
  | single len s av ret data vs result attester =>
    change t4 = records at ha
    change vs = values at hv
    subst records values
    exact easBlocks.eas_block_7840_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  | many av last ret s len data =>
    change t3 = records at ha
    change t4 = values at hv
    subst records values
    exact easBlocks.eas_block_10059_packed (immWords := wordsOf (immStore v)) (by omega) rd

theorem easAttestArrays {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema heap t3 t4 : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+22 ≤ 1024) (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) (hcd : ee.calldata.size < UInt256.size)
    (ha : recordArrayPtr site t3 t4 = heap)
    (hv : recordValuesPtr site t4 = UInt256.ofNat (allocateNext heap.toNat (32+352*(attestLoopLength site).toNat)))
    (rd : RD fork (deployedRuntime v) ee g s0 (attestArraysStartPC site) (attestArraysStartStack site schema R) mem aw rdata σ k C) :
    let len := (attestLoopLength site).toNat
    let middle := allocateNext heap.toNat (32+352*len)
    let next := allocateNext middle (32+32*len)
    if len ≤ 2^64-1 then
      if middle ≤ 2^64-1 ∧ heap.toNat ≤ middle then
        if next ≤ 2^64-1 ∧ middle ≤ next then
          ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
            (recordNextStack site schema ⟨0⟩ t3 t4 R) (attestArraysMemory mem ee.calldata heap len) aw' rdata σ k' C'
        else RDrev fork (deployedRuntime v) g s0
      else RDrev fork (deployedRuntime v) g s0
    else RDrev fork (deployedRuntime v) g s0 := by
  dsimp only
  obtain ⟨a1,k1,C1,r1⟩ := easAttestRecordsStart v site (by omega) rd
  have hrecords := easDefaultArrayAllocate v
    (by cases site <;> simp only [attestRecordsSaved,List.length_cons] <;> omega) hlo hh hheap
    (by cases site <;> simp only [attestRecordsReturnPC] <;> rw [easPatchedValidJumps v] <;> jump_dest) r1
  by_cases hl : (attestLoopLength site).toNat ≤ 2^64-1
  · rw [if_pos hl] at hrecords ⊢
    by_cases hg : allocateNext heap.toNat (32+352*(attestLoopLength site).toNat) ≤ 2^64-1 ∧
        heap.toNat ≤ allocateNext heap.toNat (32+352*(attestLoopLength site).toNat)
    · rw [if_pos hg] at hrecords ⊢
      obtain ⟨a2,k2,C2,r2⟩ := hrecords
      obtain ⟨a3,k3,C3,r3⟩ := easAttestValuesStart v site (by omega) r2
      have hm := defaultArrayMemory_view mem heap (attestLoopLength site).toNat hlo hh hl
      have hn : (UInt256.ofNat (allocateNext heap.toNat (32+352*(attestLoopLength site).toNat))).toNat =
          allocateNext heap.toNat (32+352*(attestLoopLength site).toNat) := ulit_toNat' _ (by change _ < 2^256; omega)
      have hvalues := easWordArrayAllocate v
        (by cases site <;> simp only [attestValuesSaved,List.length_cons] <;> omega)
        (by rw [hn]; exact hg.1) hm.2.2.1 hcd
        (by cases site <;> simp only [attestValuesReturnPC] <;> rw [easPatchedValidJumps v] <;> jump_dest) r3
      rw [if_pos hl,hn] at hvalues
      split at hvalues
      · rename_i hg2
        rw [if_pos hg2]
        obtain ⟨a4,k4,C4,r4⟩ := hvalues
        exact easAttestArraysDone v site (by omega) ha hv r4
      · rename_i hg2
        rw [if_neg hg2]
        exact hvalues
    · simpa only [if_neg hg] using hrecords
  · simpa only [if_neg hl] using hrecords

end Benchmarks.EAS.EAS
