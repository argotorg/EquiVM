import Benchmarks.EAS.EAS.RefUIDSites
import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.ArrayStoreIndex
import Benchmarks.EAS.EAS.WordArrayStore

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordArrayPtr (site : UIDSite) (t3 t4 : UInt256) : UInt256 :=
  match site with
  | .single .. => t4
  | .many .. => t3

def recordValuesStartPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9155
  | .many .. => UInt256.ofNat 11425

def recordValuesStack (site : UIDSite) (dummy word t1 idx t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      dummy::s6::s7::UInt256.ofNat 32::idx::UInt256.ofNat 9179::word::t3::solcAddrMask::word::t1::idx::⟨1⟩::
        s5::s8::t1::s1::s2::t4::s6::s3::s7::s4::R
  | .many s1 s2 s3 s4 s5 s6 =>
      dummy::s6::solcAddrMask::word::t1::idx::⟨1⟩::t1::s5::t3::t4::s1::s2::s3::s4::R

set_option maxRecDepth 10000 in
theorem easRecordArrayStore {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i len : Nat}
    {dummy word src t1 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+31 ≤ 1024)
    (hi : i < len) (hb : (recordArrayPtr site t3 t4).toNat+32+32*len < UInt256.size)
    (hin : (recordArrayPtr site t3 t4).toNat+32+32*len ≤ mem.size)
    (hl : memLoad (recordArrayPtr site t3 t4) mem = UInt256.ofNat len)
    (rd : RD fork (deployedRuntime v) ee g s0 (refUIDReadyPC site)
      (refUIDReadyStack site dummy word src t1 (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordValuesStartPC site)
      (recordValuesStack site (UInt256.ofNat ((recordArrayPtr site t3 t4).toNat+32+32*i))
        word t1 (UInt256.ofNat i) t3 t4 R)
      (Reasoning.Theory.writeWord mem ((recordArrayPtr site t3 t4).toNat+32+32*i) src) aw' rdata σ k' C' := by
  have hcell : (UInt256.ofNat ((recordArrayPtr site t3 t4).toNat+32+32*i)).toNat =
      (recordArrayPtr site t3 t4).toNat+32+32*i := ulit_toNat' _ (by omega)
  have hl' : memLoad (recordArrayPtr site t3 t4)
      (Reasoning.Theory.writeWord mem ((recordArrayPtr site t3 t4).toNat+32+32*i) src) = UInt256.ofNat len :=
    (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans hl
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_9099_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easArrayStoreIndex v (by simp only [List.length_cons]; omega) hi hb hin hl
      (by rw [easPatchedValidJumps v]; simp only [recordValuesStartPC]; jump_dest) hr1
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw1,k1,C1,hr1⟩ := easBlocks.eas_block_11378_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2,k2,C2,hr2⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by rw [easPatchedValidJumps v]; jump_dest) hr1
    obtain ⟨aw3,k3,C3,hr3⟩ := easBlocks.eas_block_11414_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) hr2
    simp only [easBlocks.eas_block_11414_stack,easBlocks.eas_block_11414_memory,hcell] at hr3
    obtain ⟨aw4,k4,C4,hr4⟩ := easMemoryArrayIndex v
      (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl'
      (by rw [easPatchedValidJumps v]; jump_dest) hr3
    exact ⟨aw4,k4,C4,hr4⟩

end Benchmarks.EAS.EAS
