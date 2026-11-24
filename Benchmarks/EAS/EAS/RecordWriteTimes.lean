import Benchmarks.EAS.EAS.RecordWriteStart
import Benchmarks.EAS.EAS.RuntimeBlocks_031

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordFieldsPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8775
  | .many .. => UInt256.ofNat 10990
def recordFieldsStack (site : UIDSite) (slot word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      slot :: t3 :: word :: t2 :: src :: s5 :: s8 :: t1 :: s1 :: s2 :: t4 :: s6 :: s3 :: s4 :: s7 :: R
  | .many s1 s2 s3 s4 s5 s6 =>
      s6 :: word :: slot :: t2 :: src :: t1 :: s5 :: t3 :: t4 :: s1 :: s2 :: s3 :: s4 :: R

def recordTimeAccounts (σ : AccountMap) (ee : ExecutionEnv) (mem : ByteArray) (slot src : UInt256) : AccountMap :=
  let σ1 := sstoreAccountMap ee.codeOwner σ (slot+⟨2⟩)
    (packedSliceWord (solcSlotWord σ ee (slot+⟨2⟩)) (memLoad (src+UInt256.ofNat 96) mem) 64 64)
  sstoreAccountMap ee.codeOwner σ1 (slot+⟨2⟩)
    (packedSliceWord (solcSlotWord σ1 ee (slot+⟨2⟩))
      (UInt256.land (memLoad (src+UInt256.ofNat 128) mem) (UInt256.ofNat (2^64-1))) 128 64)

theorem recordTimeAccounts_fields {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (hv : AttestationMemoryView mem src dataPtr a) (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) :
    recordTimeAccounts σ ee mem slot src = writeScalarAccounts (((attestationScalarWrites slot a).drop 3).take 2) σ ee := by
  have hf := hv.fields
  simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
    AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf
  obtain ⟨_,_,_,he,hr,_⟩ := hf
  simp only [recordTimeAccounts,hr,attestationScalarWrites,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    writeScalarAccounts,attestationTimeWrite,ScalarFieldWrite.accounts,attestationU64Loc,
    show (8 : Fin 33).val = 8 from rfl,show (8 : Fin 32).val = 8 from rfl,show (16 : Fin 32).val = 16 from rfl,
    show (8 : Nat)*8 = 64 from rfl,show (8 : Nat)*16 = 128 from rfl]
  rw [← he]
  simp only [packedSliceWord_clean _ _ 64 64 (by decide) (by decide)]

set_option maxRecDepth 10000 in
theorem easRecordWriteTimes {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word t1 t2 t3 t4 : UInt256} {a : AttestationRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+22 ≤ 1024) (hperm : ee.perm = true)
    (hv : AttestationMemoryView mem src dataPtr a)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordTimePC site)
      (recordTimeStack site mem slot word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordFieldsPC site)
      (recordFieldsStack site slot word src t1 t2 t3 t4 R) mem aw' rdata
      (writeScalarAccounts (((attestationScalarWrites slot a).drop 3).take 2) σ ee) k' C' := by
  have heq := recordTimeAccounts_fields hv σ ee slot
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_8627_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 8775)
      (recordFieldsStack (.single s1 s2 s3 s4 s5 s6 s7 s8) slot word src t1 t2 t3 t4 R) mem aw' rdata
      (recordTimeAccounts σ ee mem slot src) k' C' at hr
    exact ⟨aw',k',C',by simpa only [heq,recordFieldsPC] using hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10875_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hperm (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 10990)
      (recordFieldsStack (.many s1 s2 s3 s4 s5 s6) slot word src t1 t2 t3 t4 R) mem aw' rdata
      (recordTimeAccounts σ ee mem slot src) k' C' at hr
    exact ⟨aw',k',C',by simpa only [heq,recordFieldsPC] using hr⟩

end Benchmarks.EAS.EAS
