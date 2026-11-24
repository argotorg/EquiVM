import Benchmarks.EAS.EAS.RecordArrayStore

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordValuesPtr (site : UIDSite) (t4 : UInt256) : UInt256 :=
  match site with
  | .single _ _ _ _ _ s6 _ _ => s6
  | .many .. => t4

def recordUIDsPtr (site : UIDSite) (mem : ByteArray) : UInt256 :=
  match site with
  | .single _ _ _ _ _ _ s7 _ => memLoad (s7+UInt256.ofNat 32) mem
  | .many .. => memLoad (memLoad (UInt256.ofNat 128) mem+UInt256.ofNat 32) mem

def recordUIDStorePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9179
  | .many .. => UInt256.ofNat 11459

def recordUIDStoreStack (site : UIDSite) (dst word t1 idx t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      dst::word::t3::solcAddrMask::word::t1::idx::⟨1⟩::s5::s8::t1::s1::s2::t4::s6::s3::s7::s4::R
  | .many s1 s2 s3 s4 s5 s6 =>
      dst::word::s6::solcAddrMask::word::t1::idx::⟨1⟩::t1::s5::t3::t4::s1::s2::s3::s4::R

set_option maxRecDepth 10000 in
theorem easRecordValuesStore {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {dummy word value uidPtr t1 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+28 ≤ 1024)
    (hi : i < len) (hb : (recordValuesPtr site t4).toNat+32+32*len < UInt256.size)
    (hl : memLoad (recordValuesPtr site t4) mem = UInt256.ofNat len)
    (hvalue : memLoad (refUIDPtr site t3+UInt256.ofNat 160) mem = value)
    (hptr : recordUIDsPtr site (Reasoning.Theory.writeWord mem ((recordValuesPtr site t4).toNat+32+32*i) value) = uidPtr)
    (hu : memLoad uidPtr (Reasoning.Theory.writeWord mem ((recordValuesPtr site t4).toNat+32+32*i) value) = UInt256.ofNat len)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordValuesStartPC site)
      (recordValuesStack site dummy word t1 (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordUIDStorePC site)
      (recordUIDStoreStack site (UInt256.ofNat (uidPtr.toNat+32+32*i)) word t1 (UInt256.ofNat i) t3 t4 R)
      (Reasoning.Theory.writeWord mem ((recordValuesPtr site t4).toNat+32+32*i) value) aw' rdata σ k' C' := by
  have hcell : (UInt256.ofNat ((recordValuesPtr site t4).toNat+32+32*i)).toNat =
      (recordValuesPtr site t4).toNat+32+32*i := ulit_toNat' _ (by omega)
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    change memLoad (t3+UInt256.ofNat 160) mem = value at hvalue
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_9155_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [easBlocks.eas_block_9155_stack,hvalue] at hr1
    obtain ⟨aw2,k2,C2,hr2⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) hr1
    obtain ⟨aw3,k3,C3,hr3⟩ := easBlocks.eas_block_9171_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr2
    simp only [easBlocks.eas_block_9171_stack,easBlocks.eas_block_9171_memory,hcell] at hr3
    change memLoad (s7+UInt256.ofNat 32) _ = uidPtr at hptr
    simp only [Reasoning.Theory.writeWord] at hptr
    rw [hptr] at hr3
    obtain ⟨aw4,k4,C4,hr4⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hu
      (by rw [easPatchedValidJumps v]; jump_dest) hr3
    exact ⟨aw4,k4,C4,hr4⟩
  | many s1 s2 s3 s4 s5 s6 =>
    change memLoad (s6+UInt256.ofNat 160) mem = value at hvalue
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_11425_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [easBlocks.eas_block_11425_stack,hvalue] at hr1
    obtain ⟨aw2,k2,C2,hr2⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) hr1
    obtain ⟨aw3,k3,C3,hr3⟩ := easBlocks.eas_block_11441_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr2
    simp only [easBlocks.eas_block_11441_stack,easBlocks.eas_block_11441_memory,hcell] at hr3
    change memLoad (memLoad (UInt256.ofNat 128) _+UInt256.ofNat 32) _ = uidPtr at hptr
    simp only [Reasoning.Theory.writeWord] at hptr
    rw [hptr] at hr3
    obtain ⟨aw4,k4,C4,hr4⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hu
      (by rw [easPatchedValidJumps v]; jump_dest) hr3
    exact ⟨aw4,k4,C4,hr4⟩

end Benchmarks.EAS.EAS
