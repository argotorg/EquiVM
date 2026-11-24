import Benchmarks.EAS.EAS.MappingWordLoad

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: ISZERO/PUSH2/JUMPI with a word-valued branch operand.
theorem zeroBranch {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {pc dest word : UInt256} {R : List UInt256}
    (hstack : R.length+2 ≤ 1024)
    (hd0 : decode code pc = some (.ISZERO,.none))
    (hd1 : decode code (pc+⟨1⟩) = some (.Push .PUSH2,some (dest,2)))
    (hd4 : decode code (pc+⟨4⟩) = some (.JUMPI,.none))
    (hvalid : (D_J code 0).contains dest = true)
    (rd : RD fork code ee g s0 pc (word::R) mem aw rdata σ k C) :
    if word = ⟨0⟩ then ∃ k' C', RD fork code ee g s0 dest R mem aw rdata σ k' C'
    else ∃ k' C', RD fork code ee g s0 (pc+⟨5⟩) R mem aw rdata σ k' C' := by
  have r1 := RD.iszero rd hd0 (by omega)
  have r2 := RD.push2 r1 dest hd1 (by simp only [List.length_cons]; omega)
  by_cases hz : word = ⟨0⟩
  · rw [if_pos hz]
    have r3 := RD.jumpiT r2 (by simpa only [u256_add_assoc] using hd4)
      (by rw [hz]; decide) hvalid (by omega)
    exact ⟨_,_,r3⟩
  · rw [if_neg hz]
    have r3 := RD.jumpiNT r2 (by simpa only [u256_add_assoc] using hd4) (isZero_eq_zero_of_ne hz) (by omega)
    have r := RD.normalizePC (pc' := pc+⟨5⟩) r3 (by simp only [u256_add_assoc]; rfl)
    exact ⟨_,_,r⟩

end Benchmarks.EAS.EAS
