import Benchmarks.Midnight.LiquidateEventBudget
import Benchmarks.Midnight.LiquidateEventMemory
import Benchmarks.Midnight.LiquidateEventStatic

/-! The liquidation event's storage reads, buffer writes, and LOG4. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateEvent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root budgetRoot token mode id dp dl borrower badDebt receiver payer
      seized repaid : UInt256} {credit : Nat} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (hroot : root.toNat < 2^64) (hlo : 832 ≤ root.toNat)
    (hsize : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hslot : memLoad (UInt256.ofNat 672) mem = solcMappingSlot ⟨1⟩ id)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hb : TransferBudget budgetRoot credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5548⟩
      ([token, mode, dp, dl, borrower, badDebt, receiver, payer] ++ R) mem aw rdata σ k C) :
    let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)
    let fee := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + UInt256.ofNat 1) σ I)
      (UInt256.ofNat 128)
    let mem' := liquidateEventMemory mem root I seized repaid mode receiver payer badDebt loss fee
    (I.perm = false ∧ RDstatic midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ aw' k' C', TransferBudget budgetRoot credit mem' aw' C' ∧
      RD midnightBytecode I g s0 ⟨20488⟩
        ([⟨4⟩ + calldataWord I.calldata 4, calldataWord I.calldata 4 + ⟨100⟩,
          ⟨5734⟩, ⟨5750⟩, receiver, ⟨5543⟩, ⟨5755⟩, dp, dl, borrower, badDebt, receiver, payer] ++ R)
        mem' aw' rdata σ k' C') := by
  dsimp only
  let loss := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id) σ I) (UInt256.ofNat 128)
  let fee := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + UInt256.ofNat 1) σ I)
    (UInt256.ofNat 128)
  obtain ⟨k1, C1, hb1, rd1⟩ := liquidate_block_5548_funded (R := R) (by omega) hb rd
  have hm1 := liquidateEventHeadMemory_eq (mode := mode) (receiver := receiver) (payer := payer)
    I hroot hlo hsize hfree hseized hpaid
  rw [hm1] at rd1 hb1
  simp only [midnightBlocks.midnight_block_5548_stack, hfree, hslot] at rd1 hb1
  change RD midnightBytecode I g s0 ⟨5636⟩
    ([root, UInt256.ofNat 192, badDebt, loss, fee, root, token, dp, dl, borrower, badDebt,
      receiver, payer] ++ R)
    (liquidateEventHeadMemory mem root I seized repaid mode receiver payer) _ rdata σ k1 C1 at rd1
  by_cases hp : I.perm = true
  · have rd2 := midnightBlocks.midnight_block_5636 (R := payer :: R)
      (by simp only [List.length_cons]; omega) hp (by jump_dest) rd1
    have hb2 := transferBudgetAt (root := budgetRoot) (credit := credit) rd2 (by
      unfold midnightBlocks.midnight_block_5636_memory
      transfer_budget hb1)
    have hm2 := liquidateEventMemory_tail (mem := mem)
      I seized repaid mode receiver payer badDebt loss fee hroot
    rw [hm2] at rd2 hb2
    exact Or.inr ⟨hp, _, _, _, hb2, rd2⟩
  · exact Or.inl ⟨Bool.eq_false_iff.mpr hp, liquidate_block_5636_static (R := payer :: R)
      (by simp only [List.length_cons]; omega) (Bool.eq_false_iff.mpr hp) rd1⟩

end Benchmarks.Midnight
