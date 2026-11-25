import Benchmarks.Midnight.PositionUpdateViewBudget

variable {fork : Ethereum.Fork}

/-! The withdrawal's market-state hash before updating the position. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightWithdrawUnitsUpdateEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id user market : UInt256}
    {σ : AccountMap} {gasCredit k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hmem : 832 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget root gasCredit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨3881⟩
      (id :: user :: user :: market :: UInt256.ofNat 64 :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root gasCredit (twoWordHashMem id ⟨1⟩ mem) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨23599⟩
        (market :: id :: user :: UInt256.ofNat 3909 :: id :: user :: solcMappingSlot ⟨1⟩ id ::
          market :: UInt256.ofNat 64 :: R)
        (twoWordHashMem id ⟨1⟩ mem) aw' rdata σ k' C' := by
  have hz : memLoad (UInt256.ofNat 800) (twoWordHashMem id (UInt256.ofNat 1) mem) = ⟨0⟩ := by
    rw [memLoad_twoWordHashMem _ _ (UInt256.ofNat 800) (by decide) hmem, hzero]
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 _ _ (by omega)
  have rd1 := midnightBlocks.midnight_block_3881 hstack (by jump_dest) rd
  have hb1 := transferBudgetAt (root := root) (credit := gasCredit) rd1 (by
    simp only [midnightBlocks.midnight_block_3881_memory]
    transfer_budget hb)
  simp only [midnightBlocks.midnight_block_3881_stack,
    midnightBlocks.midnight_block_3881_memory, hzero,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl,
    wordAt0_fold, twoWordHash_fold, hz, hh] at rd1 hb1
  exact ⟨_, _, _, hb1, rd1⟩

end Benchmarks.Midnight
