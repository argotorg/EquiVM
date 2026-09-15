import Benchmarks.Auction.ReturnDataCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def revertDataWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH0, .none) ∧
  decode code (pc + ⟨2⟩) = some (.DUP1, .none) ∧
  decode code (pc + ⟨3⟩) = some (.RETURNDATACOPY, .none) ∧
  decode code (pc + ⟨4⟩) = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨5⟩) = some (.Push .PUSH0, .none) ∧
  decode code (pc + ⟨6⟩) = some (.REVERT, .none)

end Auction

namespace Reasoning.Reach

open Auction

-- LIBRARY CANDIDATE: bubble the complete returndata through an EVM REVERT.
theorem RD.revertData {code I g s0 pc R mem aw out acc k C}
    (h : RD code I g s0 pc R mem aw out acc k C) (hwf : revertDataWf code pc)
    (hov : R.length + 3 ≤ 1024) : RDrev code g s0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hwf
  have rd1 := h.returndatasize h0 (by omega)
  have rd2 := rd1.push0 h1 (by evm_ov)
  have hp2 : pc + ⟨1⟩ + ⟨1⟩ = pc + ⟨2⟩ := by rw [u256_add_assoc]; rfl
  rw [hp2] at rd2
  have rd3 := rd2.dup1 h2 (by evm_ov)
  have hp3 : pc + ⟨2⟩ + ⟨1⟩ = pc + ⟨3⟩ := by rw [u256_add_assoc]; rfl
  rw [hp3] at rd3
  obtain ⟨_, _, rd4⟩ := rd3.returndatacopySymbolic h3
    (by change 0 + out.size % UInt256.size ≤ out.size
        simpa only [Nat.zero_add] using Nat.mod_le out.size UInt256.size) (by omega)
  have hp4 : pc + ⟨3⟩ + ⟨1⟩ = pc + ⟨4⟩ := by rw [u256_add_assoc]; rfl
  rw [hp4] at rd4
  have rd5 := rd4.returndatasize h4 (by omega)
  have hp5 : pc + ⟨4⟩ + ⟨1⟩ = pc + ⟨5⟩ := by rw [u256_add_assoc]; rfl
  rw [hp5] at rd5
  have rd6 := rd5.push0 h5 (by evm_ov)
  have hp6 : pc + ⟨5⟩ + ⟨1⟩ = pc + ⟨6⟩ := by rw [u256_add_assoc]; rfl
  rw [hp6] at rd6
  exact rd6.revertSymbolic h6 (by omega)

end Reasoning.Reach
