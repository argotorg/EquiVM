import Benchmarks.Midnight.MemoryArrayIndex
import Benchmarks.Midnight.PackedArray
import Benchmarks.Midnight.TransferBudget

/-! Bounds-checked array locations retain the gas credit needed by later transfers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
theorem midnightMemoryArrayIndex_funded {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {root : UInt256} {credit : Nat} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hi : index.toNat < 2^64) (hlt : index.toNat < (memLoad ptr mem).toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hb : TransferBudget root credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19460⟩ (ptr :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit mem aw' C' ∧ RD midnightBytecode I g s0 ret
      (((ptr + UInt256.ofNat 32) + UInt256.ofNat (32 * index.toNat)) :: R)
      mem aw' rdata σ k' C' := by
  have hc : UInt256.lt index (memLoad ptr mem) = ⟨1⟩ := ult_one hlt
  have rd1 := midnightBlocks.midnight_block_19460_fallthrough (by
    simp only [List.length_cons]; omega) (by rw [hc]; rfl) rd
  have rd2 := midnightBlocks.midnight_block_19470 hstack hret rd1
  simp only [midnightBlocks.midnight_block_19470_stack, arrayIndexWord hi] at rd2
  have hb2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget hb)
  exact ⟨_, _, _, hb2, rd2⟩


theorem midnightUint128ArrayLocation_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot index ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hi : index.toNat < 128) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19480⟩ (slot :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      (UInt256.ofNat (16 * (index.toNat % 2)) :: (slot + UInt256.ofNat (index.toNat / 2)) :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.isZero (UInt256.lt index ⟨128⟩) = ⟨0⟩ := by
    rw [ult_one hi]; rfl
  have rd1 := midnightBlocks.midnight_block_19480_fallthrough (by omega) hc rd
  simp only [midnightBlocks.midnight_block_19480_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_19493 hstack hret rd1
  simp only [midnightBlocks.midnight_block_19493_stack, (uint128ArrayIndexFacts index hi).1,
    (uint128ArrayIndexFacts index hi).2.1, u256_add_comm _ slot] at rd2
  exact ⟨_, _, by omega, rd2⟩

theorem midnightMemoryArrayIndexRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr index : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hlt : (memLoad ptr mem).toNat ≤ index.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19460⟩ (ptr :: index :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_19460_taken (by omega)
    (by rw [ult_zero hlt]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_19161 (by simp only [List.length_cons]; omega) rd1

theorem midnightUint128ArrayLocationRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw slot index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hi : 128 ≤ index.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19480⟩ (slot :: index :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have rd1 := midnightBlocks.midnight_block_19480_taken hstack
    (by rw [ult_zero (a := index) (b := UInt256.ofNat 128) hi]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_19161 (by
    simp only [midnightBlocks.midnight_block_19480_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
