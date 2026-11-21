import Benchmarks.Midnight.LiquidatePositionMemory
import Benchmarks.Midnight.TransferBudget
import Benchmarks.Midnight.HealthStorage
import Benchmarks.Midnight.RuntimeBlocks_023

/-! Initialize liquidation's collateral bitmap and running debt values. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateBitmapMemory (mem : ByteArray) (bitmap : UInt256) : ByteArray :=
  writeWord mem 704 bitmap

theorem liquidateBitmapMemory_size {mem : ByteArray} (bitmap : UInt256)
    (hm : 736 ≤ mem.size) : (liquidateBitmapMemory mem bitmap).size = mem.size := by
  rw [liquidateBitmapMemory, writeWord_sparse_size]
  omega

theorem liquidateBitmapMemory_load (mem : ByteArray) (bitmap : UInt256) :
    memLoad (UInt256.ofNat 704) (liquidateBitmapMemory mem bitmap) = bitmap :=
  memLoad_writeWord _ _ _

theorem liquidateBitmapMemory_preserved {mem : ByteArray} (bitmap read : UInt256)
    (hi : read.toNat + 32 ≤ mem.size) (hd : read.toNat + 32 ≤ 704 ∨ 736 ≤ read.toNat) :
    memLoad read (liquidateBitmapMemory mem bitmap) = memLoad read mem :=
  memLoad_writeWord_preserved _ _ _ _ hi hd

theorem midnightLiquidateLoopEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw rep reverseRep pos dp dl borrower debtWord budgetRoot : UInt256}
    {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024) (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5311⟩
      ([rep, reverseRep, pos, dp, dl, borrower, debtWord] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      TransferBudget budgetRoot credit
        (liquidateBitmapMemory mem (UInt256.shiftRight debtWord ⟨128⟩)) aw' C' ∧
      RD midnightBytecode I g s0 ⟨5340⟩
        ([debtWord, reverseRep, rep, ⟨0⟩, ⟨0⟩, pos, dp, dl, borrower, low128 debtWord] ++ R)
        (liquidateBitmapMemory mem (UInt256.shiftRight debtWord ⟨128⟩)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_5311 hstack rd
  have hb1 := transferBudgetAt (root := budgetRoot) (credit := credit) rd1
    (by unfold midnightBlocks.midnight_block_5311_memory; transfer_budget hb)
  have hresult := And.intro hb1 rd1
  simp only [midnightBlocks.midnight_block_5311_stack, hz, uint128Mask_computed,
    midnightBlocks.midnight_block_5311_memory, writeWord_fold] at hresult
  exact ⟨_, _, _, hresult⟩

end Benchmarks.Midnight
