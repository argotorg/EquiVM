import Benchmarks.EAS.EAS.RecordValuesStore

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def recordEventMemory (mem : ByteArray) (dst word : UInt256) : ByteArray :=
  let mid := Reasoning.Theory.writeWord mem dst.toNat word
  Reasoning.Theory.writeWord mid (memLoad (UInt256.ofNat 64) mid).toNat word

def recordNextPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7845
  | .many .. => UInt256.ofNat 10064

def recordNextStack (site : UIDSite) (t1 idx t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 => s5::s8::s1::t1::idx::s2::t4::s6::s3::s7::s4::R
  | .many s1 s2 s3 s4 s5 _ => s5::t1::s4::t3::t4::s1::s2::s3::idx::R

set_option maxRecDepth 10000 in
theorem easRecordEvent {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {dst word t1 idx t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+19 ≤ 1024)
    (hp : ee.perm = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordUIDStorePC site)
      (recordUIDStoreStack site dst word t1 idx t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site t1 (idx+UInt256.ofNat 1) t3 t4 R)
      (recordEventMemory mem dst word) aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    exact easBlocks.eas_block_9179_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hp
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  | many s1 s2 s3 s4 s5 s6 =>
    exact easBlocks.eas_block_11459_packed (immWords := wordsOf (immStore v))
      (by omega) hp
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.EAS.EAS
