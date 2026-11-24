import Benchmarks.EAS.EAS.RecordWriteFields
import Benchmarks.EAS.EAS.BytesLength

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordBytesDecodedPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 8988
  | .many .. => UInt256.ofNat 11279
def recordBytesSaved (site : UIDSite) (word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 =>
      t3 :: word :: t2 :: src :: s5 :: s8 :: t1 :: s1 :: s2 :: t4 :: s6 :: s3 :: s4 :: s7 :: R
  | .many s1 s2 s3 s4 s5 s6 =>
      s6 :: word :: t1 :: t2 :: src :: t1 :: s5 :: t3 :: t4 :: s1 :: s2 :: s3 :: s4 :: R

set_option maxRecDepth 10000 in
theorem easRecordBytesHeader {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
      (recordBytesStack site slot word src dataPtr len t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 6418)
      (solcSlotWord σ ee (slot+⟨6⟩) :: recordBytesDecodedPC site :: dataPtr :: len :: slot ::
        recordBytesSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_8976_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',hr⟩
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_11265_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw',k',C',hr⟩

set_option maxRecDepth 10000 in
theorem easRecordBytesDecode {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesPC site)
      (recordBytesStack site slot word src dataPtr len t1 t2 t3 t4 R) mem aw rdata σ k C) :
    if storedBytesValid (solcSlotWord σ ee (slot+⟨6⟩)) then
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordBytesDecodedPC site)
        (storedBytesLengthWord (solcSlotWord σ ee (slot+⟨6⟩)) :: dataPtr :: len :: slot ::
          recordBytesSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw',k',C',hr⟩ := easRecordBytesHeader v site hstack rd
  have hd := easStoredLength v
    (by cases site <;> simp only [recordBytesSaved,List.length_cons] <;> omega)
    (by cases site <;> simp only [recordBytesDecodedPC] <;> rw [easPatchedValidJumps v] <;> jump_dest) hr
  split at hd
  · rename_i hv
    rw [if_pos hv]
    obtain ⟨k'',C'',hr'⟩ := hd
    exact ⟨aw',k'',C'',hr'⟩
  · rename_i hv
    rwa [if_neg hv]

end Benchmarks.EAS.EAS
