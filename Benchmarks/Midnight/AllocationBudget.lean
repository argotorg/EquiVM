import Benchmarks.Midnight.AllocationFunding
import Benchmarks.Midnight.TransferBudget

/-! Checked allocation preserving the transfer budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightAllocate_budget {root : UInt256} {credit : Nat}
    {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (allocationEnd ptr size) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18444⟩ (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit
        (writeWord mem 64 (allocationEnd ptr size)) aw' C' ∧
      RD midnightBytecode I g s0 ret R
        (writeWord mem 64 (allocationEnd ptr size)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18444_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18444_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18473 (by omega) hret rd1
  have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18473_memory
    transfer_budget hb)
  exact ⟨_, _, _, hb2, rd2⟩

end Benchmarks.Midnight
