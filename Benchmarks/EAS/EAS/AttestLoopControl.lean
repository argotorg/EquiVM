import Benchmarks.EAS.EAS.RecordEventEVM
import Benchmarks.EAS.EAS.RequestTimeDispatch
import Benchmarks.EAS.EAS.RuntimeBlocks_029

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def attestLoopLength : UIDSite → UInt256
  | .single s1 .. => s1
  | .many _ _ _ _ s5 _ => s5

def requestReadPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7876
  | .many .. => UInt256.ofNat 10094

def attestLoopExitPC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7853
  | .many .. => UInt256.ofNat 10072

def attestRequestArrayPtr (site : UIDSite) (mem : ByteArray) : UInt256 :=
  match site with
  | .single _ _ _ _ s5 .. => s5
  | .many .. => memLoad (UInt256.ofNat 192) mem

set_option maxRecDepth 10000 in
theorem easAttestLoopTest {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema idx t3 t4 : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+13 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordNextPC site) (recordNextStack site schema idx t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0
      (if idx.toNat < (attestLoopLength site).toNat then requestReadPC site else attestLoopExitPC site)
      (recordNextStack site schema idx t3 t4 R) mem aw' rdata σ k' C' := by
  by_cases hi : idx.toNat < (attestLoopLength site).toNat
  · rw [if_pos hi]
    have hc : UInt256.lt idx (attestLoopLength site) ≠ UInt256.ofNat 0 := by rw [ult_one hi]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_7845_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_10064_taken_packed (immWords := wordsOf (immStore v))
        (by omega) hc (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  · rw [if_neg hi]
    have hc : UInt256.lt idx (attestLoopLength site) = UInt256.ofNat 0 := ult_zero (by omega)
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      exact easBlocks.eas_block_7845_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) hc rd
    | many s1 s2 s3 s4 s5 s6 =>
      exact easBlocks.eas_block_10064_fallthrough_packed (immWords := wordsOf (immStore v)) (by omega) hc rd

set_option maxRecDepth 10000 in
theorem easAttestRequestRead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema t3 t4 : UInt256} {i len : Nat} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+16 ≤ 1024) (hi : i < len)
    (hb : (attestRequestArrayPtr site mem).toNat+32+32*len < UInt256.size)
    (hl : memLoad (attestRequestArrayPtr site mem) mem = UInt256.ofNat len)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestReadPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (requestTimePC site)
      (requestTimeStack site (UInt256.ofNat ((attestRequestArrayPtr site mem).toNat+32+32*i)) schema (UInt256.ofNat i) t3 t4 R)
      mem aw' rdata σ k' C' := by
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_7876_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by simp only [requestTimePC]; rw [easPatchedValidJumps v]; jump_dest) h1
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw1,k1,C1,h1⟩ := easBlocks.eas_block_10094_packed (immWords := wordsOf (immStore v))
      (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    exact easMemoryArrayIndex v (by simp only [List.length_cons]; omega) hi (by omega) (by omega) hl
      (by simp only [requestTimePC]; rw [easPatchedValidJumps v]; jump_dest) h1

end Benchmarks.EAS.EAS
