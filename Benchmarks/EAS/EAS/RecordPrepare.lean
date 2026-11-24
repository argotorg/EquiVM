import Benchmarks.EAS.EAS.RequestMemory
import Benchmarks.EAS.EAS.RecordCreateEVM
import Benchmarks.EAS.EAS.RefUIDSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordPreparePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7948
  | .many .. => UInt256.ofNat 10165

set_option maxRecDepth 10000 in
theorem easRecordPrepare {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap dataPtr schema idx t3 t4 : UInt256} {r : AttestationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+26 ≤ 1024)
    (hv : AttestationRequestMemoryView mem (refUIDPtr site t3) dataPtr r)
    (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordPreparePC site)
      (uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4854)
      (heap::recordCreatePC site::recordCreateStack site heap dataPtr schema idx t3 t4 r R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_7948_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    change AttestationRequestMemoryView mem t3 dataPtr r at hv
    have he : UInt256.land (UInt256.ofNat 18446744073709551615) (memLoad (t3+UInt256.ofNat 32) mem) = r.expirationTime := hv.expiration
    have ha : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (memLoad t3 mem) =
        UInt256.ofNat r.recipient.val := hv.recipient
    simp only [easBlocks.eas_block_7948_stack,refUIDPtr,hh,
      show UInt256.ofNat 128+t3 = t3+UInt256.ofNat 128 from u256_add_comm _ _,
      he,ha,hv.refUID,hv.revocable,hv.pointer] at hr
    exact ⟨aw',k',C',hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10165_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    change AttestationRequestMemoryView mem s6 dataPtr r at hv
    have he : UInt256.land (memLoad (s6+UInt256.ofNat 32) mem) (UInt256.ofNat 18446744073709551615) = r.expirationTime :=
      (u256_land_comm _ _).trans hv.expiration
    have ha : UInt256.land (memLoad s6 mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.recipient.val :=
      (u256_land_comm _ _).trans hv.recipient
    simp only [easBlocks.eas_block_10165_stack,refUIDPtr,hh,he,ha,hv.refUID,hv.revocable,hv.pointer] at hr
    exact ⟨aw',k',C',hr⟩

end Benchmarks.EAS.EAS
