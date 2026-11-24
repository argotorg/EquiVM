import Benchmarks.EAS.EAS.RecordStoreMemory
import Benchmarks.EAS.EAS.AttestationWriteSource
import Benchmarks.EAS.EAS.PackedNormalize
import Benchmarks.EAS.EAS.UIDControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordTimePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8627
  | .many .. => UInt256.ofNat 10875
def recordTimeStack (site : UIDSite) (mem : ByteArray) (slot word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      memLoad (src+UInt256.ofNat 96) mem :: (slot+⟨2⟩) :: UInt256.ofNat 8775 ::
      slot :: t3 :: word :: t2 :: src :: s5 :: s8 :: t1 :: s1 :: s2 :: t4 :: s6 :: s3 :: s4 :: s7 :: R
  | .many s1 s2 s3 s4 s5 s6 =>
      UInt256.ofNat (2^256-2^128+2^64-1) :: memLoad (src+UInt256.ofNat 96) mem :: (slot+⟨2⟩) :: UInt256.ofNat 10990 ::
      s6 :: word :: slot :: t2 :: src :: t1 :: s5 :: t3 :: t4 :: s1 :: s2 :: s3 :: s4 :: R

def recordFirstAccounts (σ : AccountMap) (ee : ExecutionEnv) (mem : ByteArray) (slot src : UInt256) : AccountMap :=
  let σ1 := sstoreAccountMap ee.codeOwner σ slot (memLoad src mem)
  let σ2 := sstoreAccountMap ee.codeOwner σ1 (slot+⟨1⟩) (memLoad (src+UInt256.ofNat 32) mem)
  sstoreAccountMap ee.codeOwner σ2 (slot+⟨2⟩)
    (UInt256.lor (UInt256.land (solcSlotWord σ2 ee (slot+⟨2⟩)) (UInt256.ofNat (2^256-2^64)))
      (UInt256.land (UInt256.land (memLoad (src+UInt256.ofNat 64) mem) (UInt256.ofNat (2^64-1))) (UInt256.ofNat (2^64-1))))

theorem recordFirstAccounts_fields {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (hv : AttestationMemoryView mem src dataPtr a) (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) :
    recordFirstAccounts σ ee mem slot src = writeScalarAccounts ((attestationScalarWrites slot a).take 3) σ ee := by
  have hf := hv.fields
  simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
    AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf
  obtain ⟨hu,hs,ht,_⟩ := hf
  simp only [recordFirstAccounts,hu,hs,ht,attestationScalarWrites,List.take_succ_cons,List.take_zero,
    writeScalarAccounts,attestationWordWrite,attestationTimeWrite,ScalarFieldWrite.accounts,
    bytes32Loc,attestationU64Loc,Fin.val_zero,show (32 : Fin 33).val = 32 from rfl,
    show (8 : Fin 33).val = 8 from rfl,Nat.mul_zero,show (8 : Nat)*32 = 256 from rfl,
    show (8 : Nat)*8 = 64 from rfl,packedSliceWord_full]
  simp only [packedSliceWord_low,setLowWord_eq]

theorem easRecordWriteStart {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr word bump t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+21 ≤ 1024) (hperm : ee.perm = true)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidAvailablePC site)
      (word::bump::uidSaved site src (t1::t2::t3::t4::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordTimePC site)
      (recordTimeStack site (recordStoreMemory mem src word) (dbSlot word) word src t1 t2 t3 t4 R)
      (recordStoreMemory mem src word) aw' rdata
      (writeScalarAccounts ((attestationScalarWrites (dbSlot word) {a with uid := word}).take 3) σ ee) k' C' := by
  let m := recordStoreMemory mem src word
  have hv := recordStoreMemory_view hview word hdata hb
  have hfields := recordFirstAccounts_fields hv σ ee (dbSlot word)
  have hhash := recordStoreMemory_hash mem src word
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_8511_packed (immWords := wordsOf (immStore v)) hstack hperm rd
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 8627)
      (recordTimeStack (.single s1 s2 s3 s4 s5 s6 s7 s8) m (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m)
        word src t1 t2 t3 t4 R) m aw' rdata
      (recordFirstAccounts σ ee m (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m) src) k' C' at hr
    refine ⟨aw',k',C',?_⟩
    simpa only [m,hhash,hfields,recordTimePC] using hr
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10727_packed (immWords := wordsOf (immStore v)) (by omega) hperm rd
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 10875)
      (recordTimeStack (.many s1 s2 s3 s4 s5 s6) m (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m)
        word src t1 t2 t3 t4 R) m aw' rdata
      (recordFirstAccounts σ ee m (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m) src) k' C' at hr
    refine ⟨aw',k',C',?_⟩
    simpa only [m,hhash,hfields,recordTimePC] using hr

end Benchmarks.EAS.EAS
