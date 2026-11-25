import Benchmarks.Midnight.SettlementTrace
import Benchmarks.Midnight.MemoryFunding

variable {fork : Ethereum.Fork}

/-! The settlement-fee storage read retains memory funding across SLOAD. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem settlementRead_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hmem : 64 ≤ mem.size)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) ≠ ⟨0⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨21835⟩ (id :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (twoWordHashMem id ⟨1⟩ mem) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨21863⟩
        (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I :: R)
        (twoWordHashMem id ⟨1⟩ mem) aw' rdata σ k' C' := by
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 1) mem) = solcMappingSlot ⟨1⟩ id :=
    twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) hmem
  -- The generated block hides SLOAD's cost. Retain it using the monotone read primitive.
  let r0 := rd
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := RD.genMstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have ha11 := memoryFundingAt (credit := credit) r11 (by memory_fund ha)
  obtain ⟨_, _, hC12, r12⟩ := RD.sloadMono r11 (by native_decide) (by evm_ov)
  have ha12 := ha11.mono hC12
  have r13 := r12.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r16 := r15.shr (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 16904) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) (by
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh]
    exact isZero_eq_zero_of_ne hspace) (by evm_ov)
  have rf := RD.normalizePC (pc' := UInt256.ofNat 21863) r20 (by native_decide)
  have haf := memoryFundingAt (credit := credit) rf (by memory_fund ha12)
  simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh] at rf haf
  exact ⟨_, _, _, haf, rf⟩

end Benchmarks.Midnight
