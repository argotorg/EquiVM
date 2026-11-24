import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: mapping loads that retain their arbitrary word key on the stack.
def mappingWordLoadWf (code : ByteArray) (pc slot : UInt256) : Prop :=
  decode code pc = some (.DUP1,.none) ∧
  decode code (pc+⟨1⟩) = some (.Push .PUSH1,some (⟨0⟩,1)) ∧
  decode code (pc+⟨3⟩) = some (.MSTORE,.none) ∧
  decode code (pc+⟨4⟩) = some (.Push .PUSH1,some (slot,1)) ∧
  decode code (pc+⟨6⟩) = some (.Push .PUSH1,some (⟨32⟩,1)) ∧
  decode code (pc+⟨8⟩) = some (.MSTORE,.none) ∧
  decode code (pc+⟨9⟩) = some (.Push .PUSH1,some (⟨64⟩,1)) ∧
  decode code (pc+⟨11⟩) = some (.Push .PUSH1,some (⟨0⟩,1)) ∧
  decode code (pc+⟨13⟩) = some (.KECCAK256,.none) ∧
  decode code (pc+⟨14⟩) = some (.SLOAD,.none)

theorem mappingWordLoad {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {pc slot key : UInt256} {R : List UInt256}
    (hstack : R.length+3 ≤ 1024) (hwf : mappingWordLoadWf code pc slot)
    (rd : RD fork code ee g s0 pc (key::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork code ee g s0 (pc+⟨15⟩) (solcSlotWord σ ee (solcMappingSlot slot key)::key::R)
      (twoWordHashMem key slot mem) aw' rdata σ k' C' := by
  obtain ⟨hd0,hd1,hd3,hd4,hd6,hd8,hd9,hd11,hd13,hd14⟩ := hwf
  have r1 := RD.dup1 rd hd0 (by omega)
  have r2 := RD.push1 r1 ⟨0⟩ hd1 (by simp only [List.length_cons]; omega)
  have r3 := RD.genMstore r2 (by simpa only [u256_add_assoc] using hd3) (by simp only [List.length_cons]; omega)
  have r4 := RD.push1 r3 slot (by simpa only [u256_add_assoc] using hd4) (by simp only [List.length_cons]; omega)
  have r5 := RD.push1 r4 ⟨32⟩ (by simpa only [u256_add_assoc] using hd6) (by simp only [List.length_cons]; omega)
  have r6 := RD.genMstore r5 (by simpa only [u256_add_assoc] using hd8) (by simp only [List.length_cons]; omega)
  have r7 := RD.push1 r6 ⟨64⟩ (by simpa only [u256_add_assoc] using hd9) (by simp only [List.length_cons]; omega)
  have r8 := RD.push1 r7 ⟨0⟩ (by simpa only [u256_add_assoc] using hd11) (by simp only [List.length_cons]; omega)
  have r9 := RD.genKeccak256 r8 (by simpa only [u256_add_assoc] using hd13) (by simp only [List.length_cons]; omega)
  have hk : keccakWord (⟨0⟩ : UInt256) ⟨64⟩ (twoWordHashMem key slot mem) = solcMappingSlot slot key :=
    twoWordHashMem_solcMappingSlot_any slot key mem
  change RD fork code ee g s0 _ (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key slot mem)::key::R)
    (twoWordHashMem key slot mem) _ rdata σ _ _ at r9
  rw [hk] at r9
  obtain ⟨k',C',r10⟩ := RD.sload r9 (by simpa only [u256_add_assoc] using hd14) (by simp only [List.length_cons]; omega)
  have r := RD.normalizePC (pc' := pc+⟨15⟩) r10 (by simp only [u256_add_assoc]; rfl)
  exact ⟨_,k',C',r⟩

end Benchmarks.EAS.EAS
