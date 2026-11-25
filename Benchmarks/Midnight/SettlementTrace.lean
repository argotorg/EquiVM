import Benchmarks.Midnight.SettlementIntervalTrace
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.RuntimeBlocks_063
import Benchmarks.Midnight.RuntimeBlocks_081

variable {fork : Ethereum.Fork}

/-! The settlement-fee storage read, market guard, and internal routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem settlementInternalTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {id time ret : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hmem : 64 ≤ mem.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨21835⟩ (id :: time :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ret
      (settlementFeeValue (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) time :: R)
      (twoWordHashMem id ⟨1⟩ mem) aw' rdata σ k' C' := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 1) mem) = solcMappingSlot ⟨1⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) hmem
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21835_fallthrough_packed
    (by simp; omega) (by
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
        hh]
      exact isZero_eq_zero_of_ne hspace) rd
  simp only [midnightBlocks.midnight_block_21835_fallthrough_stack,
    midnightBlocks.midnight_block_21835_fallthrough_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hh] at rd1
  obtain ⟨k2, C2, rd2⟩ := settlementComputeTrace hstack hret rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem settlementInternalTraceRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {id : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hmem : 64 ≤ mem.size)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) = ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨21835⟩ (id :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 1) mem) = solcMappingSlot ⟨1⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) hmem
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21835_taken_packed hstack (by
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
        hh]
      change UInt256.isZero (marketTickSpacing
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)) ≠ ⟨0⟩
      rw [hspace]; decide) (by native_decide) rd
  exact midnightBlocks.midnight_block_16904 (by
    simp only [midnightBlocks.midnight_block_21835_taken_stack, List.length_cons]
    omega) rd1

end Benchmarks.Midnight
