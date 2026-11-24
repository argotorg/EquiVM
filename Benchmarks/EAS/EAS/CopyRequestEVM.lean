import Benchmarks.EAS.EAS.CopyRequestBegin
import Benchmarks.EAS.EAS.CopyRequestBytes

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestCopyRunValid (cd : ByteArray) (src stop heap : UInt256) : Prop :=
  UInt256.slt (UInt256.sub stop src) ⟨192⟩ = ⟨0⟩ ∧
  (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192) ∧
  requestCopyFieldsValid cd src ∧
  requestCopyBytesValid cd src (requestCopyWord cd src 128) stop (UInt256.ofNat (allocateNext heap.toNat 192))
instance (cd : ByteArray) (src stop heap : UInt256) : Decidable (requestCopyRunValid cd src stop heap) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def requestCopyMemory (mem cd : ByteArray) (src heap : UInt256) : ByteArray :=
  requestCopyBytesMemory
    (requestCopyFieldsMemory (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 192))) cd heap src)
    cd src (requestCopyWord cd src 128) (UInt256.ofNat (allocateNext heap.toNat 192)) heap

-- Expose the two branches before substituting compound calldata addresses.
theorem easCopyRequestBytes_branches {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src off stop heap record ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+13 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5459⟩ (off::src::stop::record::ret::R) mem aw rdata σ k C) :
    (requestCopyBytesValid ee.calldata src off stop heap →
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
        (requestCopyBytesMemory mem ee.calldata src off heap record) aw' rdata σ k' C') ∧
    (¬ requestCopyBytesValid ee.calldata src off stop heap → RDrev fork (deployedRuntime v) g s0) := by
  have h := easCopyRequestBytes v hstack hfree hret rd
  constructor
  · intro hv
    rwa [if_pos hv] at h
  · intro hv
    rwa [if_neg hv] at h

theorem easCopyRequest {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap stop ret : UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+14 ≤ 1024) (hlo : 96 ≤ heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨5344⟩ (src::stop::ret::R) mem aw rdata σ k C) :
    if requestCopyRunValid ee.calldata src stop heap then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap::R)
        (requestCopyMemory mem ee.calldata src heap) aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  have hb := easCopyRequestBegin v (by omega) hfree rd
  by_cases hhead : UInt256.slt (UInt256.sub stop src) ⟨192⟩ = ⟨0⟩
  · rw [if_pos hhead] at hb
    by_cases ha : allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192
    · rw [if_pos ha] at hb
      obtain ⟨a1,k1,C1,r1⟩ := hb
      have hf := easCopyRequestFields v (by omega) hh r1
      by_cases hfields : requestCopyFieldsValid ee.calldata src
      · rw [if_pos hfields] at hf
        obtain ⟨a2,k2,C2,r2⟩ := hf
        have hm : memLoad (UInt256.ofNat 64)
            (requestCopyFieldsMemory (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 192)))
              ee.calldata heap src) = UInt256.ofNat (allocateNext heap.toNat 192) :=
          writeWordSequence_setFree_load64 mem heap.toNat _ _ hlo
        have hp := easCopyRequestBytes_branches (mem := requestCopyFieldsMemory
            (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 192))) ee.calldata heap src)
          (heap := UInt256.ofNat (allocateNext heap.toNat 192)) (R := heap::R) v
          (by simpa only [List.length_cons,Nat.add_assoc] using hstack) hm hret r2
        by_cases hbytes : requestCopyBytesValid ee.calldata src (requestCopyWord ee.calldata src 128)
            stop (UInt256.ofNat (allocateNext heap.toNat 192))
        · rw [if_pos ⟨hhead,ha,hfields,hbytes⟩]
          exact hp.1 hbytes
        · rw [if_neg (fun h => hbytes h.2.2.2)]
          exact hp.2 hbytes
      · rw [if_neg hfields] at hf
        rw [if_neg (fun h => hfields h.2.2.1)]
        exact hf
    · rw [if_neg ha] at hb
      rw [if_neg (fun h => ha h.2.1)]
      exact hb
  · rw [if_neg hhead] at hb
    rw [if_neg (fun h => hhead h.1)]
    exact hb

end Benchmarks.EAS.EAS
