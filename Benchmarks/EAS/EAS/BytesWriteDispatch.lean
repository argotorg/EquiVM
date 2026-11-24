import Benchmarks.EAS.EAS.BytesCleanDispatch
import Benchmarks.EAS.EAS.RuntimeBlocks_036

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def bytesShortPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9022
  | .many .. => UInt256.ofNat 11304
def bytesLongPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9355
  | .many .. => UInt256.ofNat 11587
def bytesWrittenPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 9085
  | .many .. => UInt256.ofNat 11367
def bytesWriteSaved (site : UIDSite) (word src t1 t2 t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 => t3::word::t1::t2::src::s5::s8::t1::s1::s2::t4::s6::s3::s7::s4::R
  | .many .. => recordBytesSaved site word src t1 t2 t3 t4 R

set_option maxRecDepth 10000 in
theorem easBytesWriteDispatch {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len old t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesCleanPC site)
      (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (if len.toNat < 32 then bytesShortPC site else bytesLongPC site)
      (dataPtr::UInt256.ofNat 32::len::slot::bytesWriteSaved site word src t1 t2 t3 t4 R) mem aw' rdata σ k' C' := by
  by_cases hs : len.toNat < 32
  · rw [if_pos hs]
    have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) = ⟨0⟩ := by
      rw [ugt_zero (by change len.toNat ≤ 31; omega)]
      decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_8997_fallthrough_packed (immWords := wordsOf (immStore v))
        (by omega) hc rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_11288_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [bytesWriteSaved,recordBytesSaved,List.length_cons]; omega) hc rd
  · rw [if_neg hs]
    have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) ≠ ⟨0⟩ := by
      rw [ugt_one (by change 31 < len.toNat; omega)]
      decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_8997_taken_packed (immWords := wordsOf (immStore v))
        (by omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_11288_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [bytesWriteSaved,recordBytesSaved,List.length_cons]; omega) hc
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.EAS.EAS
