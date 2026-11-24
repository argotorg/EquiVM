import Benchmarks.EAS.EAS.NewRecordSource
import Benchmarks.EAS.EAS.RecordCreateMemory
import Benchmarks.EAS.EAS.UIDSites
import Benchmarks.EAS.EAS.RuntimeBlocks_034

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordCreatePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8020
  | .many .. => UInt256.ofNat 10233
def recordCreateAttester (site : UIDSite) (mem : ByteArray) : UInt256 :=
  match site with
  | .single _ _ _ _ _ _ _ s8 => UInt256.land s8 solcAddrMask
  | .many .. => UInt256.land (memLoad (UInt256.ofNat 160) mem) solcAddrMask
def recordCreateStack (site : UIDSite) (src dataPtr schema idx t3 t4 : UInt256)
    (r : AttestationRequestRecord) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
    src::schema::r.expirationTime::r.refUID::UInt256.ofNat r.recipient.val::r.revocable.toUInt256::dataPtr::
      s1::s2::s3::s4::s5::s6::s7::s8::src::schema::idx::t3::t4::R
  | .many s1 s2 s3 s4 s5 s6 =>
    r.expirationTime::r.refUID::UInt256.ofNat r.recipient.val::r.revocable.toUInt256::dataPtr::
      s1::s2::s3::s4::s5::s6::src::schema::idx::t3::t4::R

set_option maxRecDepth 10000 in
theorem easRecordCreate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr schema idx t3 t4 : UInt256} {r : AttestationRequestRecord} {attester : AccountAddress} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+25 ≤ 1024)
    (hlo : 192 ≤ src.toNat) (hmem : 192 ≤ mem.size) (hb : src.toNat+320 < UInt256.size)
    (ha : recordCreateAttester site mem = UInt256.ofNat attester.val)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordCreatePC site)
      (recordCreateStack site src dataPtr schema idx t3 t4 r R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidStartPC site)
      (⟨0⟩::uidSaved site src (schema::idx::t3::t4::R))
      (recordCreateMemory mem src dataPtr (newAttestation r schema (easTimeWord ee) attester)) aw' rdata σ k' C' := by
  have hn (n : Nat) (h : n ≤ 288) : (src+UInt256.ofNat n).toNat = src.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_8020_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd
    have hm : easBlocks.eas_block_8020_memory (ee := ee) (mem := mem) (x0 := src) (x1 := schema)
        (x2 := r.expirationTime) (x3 := r.refUID) (x4 := UInt256.ofNat r.recipient.val)
        (x5 := r.revocable.toUInt256) (x6 := dataPtr) (x14 := s8) (x15 := src) =
        recordCreateMemory mem src dataPtr (newAttestation r schema (easTimeWord ee) attester) := by
      change UInt256.land s8 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat attester.val at ha
      simp only [easBlocks.eas_block_8020_memory,← writeWord_as_write,
        show UInt256.ofNat 32+src = src+UInt256.ofNat 32 from u256_add_comm _ _,
        show UInt256.ofNat 96+src = src+UInt256.ofNat 96 from u256_add_comm _ _,
        hn 32 (by decide),hn 64 (by decide),hn 96 (by decide),hn 128 (by decide),hn 160 (by decide),
        hn 192 (by decide),hn 224 (by decide),hn 256 (by decide),hn 288 (by decide),ha,
        show UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.ofNat ee.header.timestamp) = easTimeWord ee from u256_land_comm _ _,
        recordCreateMemory,newAttestation,AttestationRecord.words,List.cons_append,List.nil_append,writeWordSequence,Nat.add_assoc]
      rfl
    exact ⟨aw',k',C',by simpa only [hm] using hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10233_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) rd
    have hm : easBlocks.eas_block_10233_memory (ee := ee) (mem := mem)
        (x0 := r.expirationTime) (x1 := r.refUID) (x2 := UInt256.ofNat r.recipient.val)
        (x3 := r.revocable.toUInt256) (x4 := dataPtr) (x11 := src) (x12 := schema) =
        recordCreateMemory mem src dataPtr (newAttestation r schema (easTimeWord ee) attester) := by
      change UInt256.land (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat attester.val at ha
      simp only [easBlocks.eas_block_10233_memory,← writeWord_as_write,
        hn 32 (by decide),hn 64 (by decide),hn 96 (by decide),hn 128 (by decide),hn 160 (by decide),
        hn 192 (by decide),hn 224 (by decide),hn 256 (by decide),hn 288 (by decide)]
      have hk (m : ByteArray) (off : Nat) (w : UInt256) (hl : 192 ≤ off) (hi : 192 ≤ m.size) :
          memLoad (UInt256.ofNat 160) (Reasoning.Theory.writeWord m off w) = memLoad (UInt256.ofNat 160) m :=
        memLoad_write_below _ _ _ _ hl hi
      simp (disch := (first | omega | (simp only [writeWord_sparse_size]; omega))) only [hk]
      rw [ha]
      simp only [recordCreateMemory,newAttestation,AttestationRecord.words,List.cons_append,List.nil_append,writeWordSequence,Nat.add_assoc]
      rfl
    exact ⟨aw',k',C',by simpa only [hm] using hr⟩

end Benchmarks.EAS.EAS
