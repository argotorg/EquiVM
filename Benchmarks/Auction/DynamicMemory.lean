import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: symbolic memory operations, retaining the exact expansion cost and result.
def expandedWords (aw offset size : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat offset.toNat size.toNat)

def expansionCost (aw offset size : UInt256) : Nat :=
  Cₘ (expandedWords aw offset size) - Cₘ aw

def loadedWord (mem : ByteArray) (aw offset : UInt256) : UInt256 :=
  if offset.toNat ≥ mem.size ∨ offset ≥ aw * ⟨32⟩ then ⟨0⟩ else
    UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding offset.toNat 32))

end Auction

namespace Reasoning.Reach

open Auction

theorem RD.mloadSymbolic {code I g s0 pc offset R mem aw rdata acc k C}
    (h : RD code I g s0 pc (offset :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none)) (hov : R.length + 1 ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) (loadedWord mem aw offset :: R)
      mem (expandedWords aw offset ⟨32⟩) rdata acc (k + 1)
      (C + (expansionCost aw offset ⟨32⟩ + 3)) := by
  apply h.mload (expansionCost aw offset ⟨32⟩) _ _ hdec _ rfl rfl hov
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
  rfl

theorem RD.mstoreSymbolic {code I g s0 pc offset value R mem aw rdata acc k C}
    (h : RD code I g s0 pc (offset :: value :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hov : R.length ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) R (value.toByteArray.write 0 mem offset.toNat 32)
      (expandedWords aw offset ⟨32⟩) rdata acc (k + 1)
      (C + (expansionCost aw offset ⟨32⟩ + 3)) := by
  exact h.mstore (expansionCost aw offset ⟨32⟩) _ _ hdec
    (fun _ haw hstk => mstoreCost_of_stack haw hstk rfl) rfl rfl hov

theorem RD.log1Symbolic {code I g s0 pc offset size topic R mem aw rdata acc k C}
    (h : RD code I g s0 pc (offset :: size :: topic :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG1, .none)) (hperm : I.perm = true)
    (hov : R.length ≤ 1024) :
    ∃ k' C', RD code I g s0 (pc + ⟨1⟩) R mem (expandedWords aw offset size)
      rdata acc k' C' := by
  refine ⟨_, _, h.log1 (expansionCost aw offset size) _ hdec hperm ?_ rfl hov⟩
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
  rfl

theorem RD.revertSymbolic {code I g s0 pc offset size R mem aw rdata acc k C}
    (h : RD code I g s0 pc (offset :: size :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none)) (hov : R.length ≤ 1024) :
    RDrev code g s0 := by
  apply h.rev (expansionCost aw offset size) hdec _ hov
  intro s haw hstk
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
  rfl

end Reasoning.Reach
