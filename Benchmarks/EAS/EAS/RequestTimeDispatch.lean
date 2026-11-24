import Benchmarks.EAS.EAS.RequestTimeControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

def requestTimePC : UIDSite → UInt256
  | .single .. => UInt256.ofNat 7897
  | .many .. => UInt256.ofNat 10114

def requestTimeStack (site : UIDSite) (cell schema idx t3 t4 : UInt256) (R : List UInt256) : List UInt256 :=
  match site with
  | .single s1 s2 s3 s4 s5 s6 s7 s8 => cell::s3::s4::s5::s6::s7::s8::s1::schema::idx::s2::t4::R
  | .many s1 s2 s3 s4 s5 _ => cell::s3::s4::s5::s2::s1::schema::idx::t3::t4::R

set_option maxRecDepth 10000 in
theorem easRequestTimeDispatch {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {cell schema idx t3 t4 expire : UInt256} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+17 ≤ 1024) (hp : memLoad cell mem = refUIDPtr site t3)
    (he : UInt256.land (memLoad (refUIDPtr site t3+UInt256.ofNat 32) mem) easUint64Mask = expire)
    (rd : RD fork (deployedRuntime v) ee g s0 (requestTimePC site) (requestTimeStack site cell schema idx t3 t4 R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0
      (if expire = ⟨0⟩ then requestTimeRequirePC site else requestTimeComparePC site)
      (expire::UInt256.isZero (UInt256.isZero expire)::uidSaved site (refUIDPtr site t3+UInt256.ofNat 32) (schema::idx::t3::t4::R))
      mem aw' rdata σ k' C' := by
  change UInt256.land (memLoad (refUIDPtr site t3+UInt256.ofNat 32) mem) (UInt256.ofNat 18446744073709551615) = expire at he
  by_cases hz : expire = ⟨0⟩
  · rw [if_pos hz]
    have hc : UInt256.isZero (UInt256.isZero expire) = UInt256.ofNat 0 := by rw [hz]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_7897_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hp,he]; exact hc) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_7897_fallthrough_stack,hp,he] using hr⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10114_fallthrough_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hp,he]; exact hc) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_10114_fallthrough_stack,hp,he] using hr⟩
  · rw [if_neg hz]
    have hc : UInt256.isZero (UInt256.isZero expire) ≠ UInt256.ofNat 0 := by
      rw [isZero_eq_zero_of_ne hz]; decide
    cases site with
    | single s1 s2 s3 s4 s5 s6 s7 s8 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_7897_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hp,he]; exact hc)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_7897_taken_stack,hp,he] using hr⟩
    | many s1 s2 s3 s4 s5 s6 =>
      obtain ⟨aw',k',C',hr⟩ := easBlocks.eas_block_10114_taken_packed (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (by rw [hp,he]; exact hc)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw',k',C',by simpa only [easBlocks.eas_block_10114_taken_stack,hp,he] using hr⟩

end Benchmarks.EAS.EAS
