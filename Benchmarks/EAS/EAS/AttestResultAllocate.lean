import Benchmarks.EAS.EAS.DefaultResultAllocate
import Benchmarks.EAS.EAS.AllocateBounds
import Benchmarks.EAS.EAS.StructEncodeViews
import Benchmarks.EAS.EAS.RuntimeBlocks_029
import Benchmarks.EAS.EAS.RuntimeBlocks_033

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive AttestCallKind where
  | single | many

def AttestCallKind.firstReturn : AttestCallKind → UInt256
  | .single => ⟨7660⟩ | .many => ⟨9875⟩
def AttestCallKind.secondReturn : AttestCallKind → UInt256
  | .single => ⟨7672⟩ | .many => ⟨9889⟩
def attestFirstSaved (kind : AttestCallKind) (schema data attester available last ret : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => attester::data::available::schema::ret::R
  | .many => available::last::ret::schema::R

def attestSecondSaved (kind : AttestCallKind) (schema data attester available last ret len : UInt256) (R : List UInt256) : List UInt256 :=
  match kind with
  | .single => schema::attester::data::available::len::ret::R
  | .many => schema::available::last::ret::len::R

def attestResultsMemory (mem : ByteArray) (heap : UInt256) : ByteArray :=
  defaultResultMemory (defaultResultMemory mem heap) (UInt256.ofNat (allocateNext heap.toNat 64))

theorem easAttestSecondResultStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data attester available last ret len first : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+8 ≤ 1024)
    (hlen : memLoad data mem = len) (hreg : kind = .many → memLoad (UInt256.ofNat 192) mem = data)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.firstReturn
      (first::attestFirstSaved kind schema data attester available last ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨7214⟩
      (kind.secondReturn::attestSecondSaved kind schema data attester available last ret len R) mem aw' rdata σ k' C' := by
  have hd : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7214) = true := by rw [easPatchedValidJumps v]; jump_dest
  cases kind with
  | single =>
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_7660_packed (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hd rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_7660_stack,hlen] using h⟩
  | many =>
    obtain ⟨a,j,D,h⟩ := easBlocks.eas_block_9875_packed (immWords := wordsOf (immStore v)) (by omega) hd rd
    exact ⟨a,j,D,by simpa only [easBlocks.eas_block_9875_stack,hreg rfl,hlen] using h⟩

theorem easAttestResultAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema data attester available last ret len heap : UInt256} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+13 ≤ 1024)
    (hlo : 224 ≤ data.toNat) (hspan : data.toNat+32 ≤ heap.toNat) (hcovered : data.toNat+32 ≤ mem.size)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hlen : memLoad data mem = len) (hreg : kind = .many → memLoad (UInt256.ofNat 192) mem = data)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨7214⟩
      (kind.firstReturn::attestFirstSaved kind schema data attester available last ret R) mem aw rdata σ k C) :
    if allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128 then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 kind.secondReturn
        (UInt256.ofNat (allocateNext heap.toNat 64)::attestSecondSaved kind schema data attester available last ret len R)
        (attestResultsMemory mem heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have h64 : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  have h128 := allocateNext_128 hh
  have hfirst := easDefaultResultAllocate v
    (by cases kind <;> simp only [attestFirstSaved,List.length_cons] <;> omega) hheap
    (by cases kind <;> simp only [AttestCallKind.firstReturn] <;> rw [easPatchedValidJumps v] <;> jump_dest) rd
  by_cases hg1 : allocateNext heap.toNat 64 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 64
  · rw [if_pos hg1] at hfirst
    obtain ⟨a1,k1,C1,r1⟩ := hfirst
    have hp := defaultResultMemory_prefix mem heap
    have hlen1 : memLoad data (defaultResultMemory mem heap) = len :=
      (memLoad_of_prefix hp data (by omega) hspan hcovered).trans hlen
    have hreg1 : kind = .many → memLoad (UInt256.ofNat 192) (defaultResultMemory mem heap) = data := by
      intro hk
      exact (memLoad_of_prefix hp (UInt256.ofNat 192) (by decide) (by change 224 ≤ heap.toNat; omega)
        (by change 224 ≤ mem.size; omega)).trans (hreg hk)
    obtain ⟨a2,k2,C2,r2⟩ := easAttestSecondResultStart v kind (by omega) hlen1 hreg1 r1
    have hn : (UInt256.ofNat (allocateNext heap.toNat 64)).toNat = allocateNext heap.toNat 64 :=
      ulit_toNat' _ (by change _ < 2^256; omega)
    have hnext : allocateNext (allocateNext heap.toNat 64) 64 = allocateNext heap.toNat 128 := by
      have h := fixedAllocation_next .bytes64 hg1.1
      change allocateNext (allocateNext heap.toNat 64) 64 = allocateNext heap.toNat 64+64 at h
      rw [h,h64,h128]
    have hsecond := easDefaultResultAllocate v
      (by cases kind <;> simp only [attestSecondSaved,List.length_cons] <;> omega)
      (defaultResultMemory_heap mem heap (by omega))
      (by cases kind <;> simp only [AttestCallKind.secondReturn] <;> rw [easPatchedValidJumps v] <;> jump_dest) r2
    rw [hn,hnext] at hsecond
    have hge1 : heap.toNat ≤ allocateNext heap.toNat 128 := by rw [h128]; omega
    have hge2 : allocateNext heap.toNat 64 ≤ allocateNext heap.toNat 128 := by rw [h64,h128]; omega
    simpa only [hge1,hge2,and_true,attestResultsMemory] using hsecond
  · rw [if_neg hg1] at hfirst
    rw [if_neg (by rw [h64] at hg1; rw [h128]; omega)]
    exact hfirst

end Benchmarks.EAS.EAS
