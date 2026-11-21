import Benchmarks.Midnight.StorageWriteGas
import Benchmarks.Midnight.PackedStorageSourceState
import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.RuntimeBlocks_047

/-! The first trade SSTORE, followed by the ordered read of buyer pending fees. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightTakeBuyerDebtWrite {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value slot w0 w1 w2 : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨12353⟩
      ([value, uint128Mask, slot, w0, w1, ⟨2⟩, w2, uint128Mask] ++ R) mem aw rdata σ k C) :
    (I.perm = false ∧ RDstatic midnightBytecode g s0) ∨
    (I.perm = true ∧ ∃ k' C',
      MemoryFunding credit mem (M aw (UInt256.ofNat 224) ⟨32⟩) C' ∧
      RD midnightBytecode I g s0 ⟨20456⟩
        ([UInt256.shiftRight
            (solcSlotWordAt slot (storeLow128Accounts σ I (slot + ⟨2⟩) value) I)
            (UInt256.ofNat 128), memLoad (UInt256.ofNat 224) mem, ⟨4216⟩, ⟨12386⟩,
          slot, w0, w1, ⟨2⟩, w2, uint128Mask] ++ R)
        mem (M aw (UInt256.ofNat 224) ⟨32⟩) rdata
        (storeLow128Accounts σ I (slot + ⟨2⟩) value) k' C') := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup6 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc8, r8⟩ := RD.sloadMono r7 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.or (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  by_cases hp : I.perm = true
  · obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hp (by native_decide) (by evm_ov)
    have r15 := r14.push2 (UInt256.ofNat 12386) (by native_decide) (by evm_ov)
    have r16 := r15.push2 (UInt256.ofNat 4216) (by native_decide) (by evm_ov)
    have r17 := r16.dup3 (by native_decide) (by evm_ov)
    obtain ⟨_, _, hc18, r18⟩ := RD.sloadMono r17 (by native_decide) (by evm_ov)
    have ha18 := memoryFundingAt (credit := credit) r18 (ha.mono (by omega))
    have r19 := r18.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
    have r20 := r19.shr (by native_decide) (by evm_ov)
    have r21 := r20.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
    have r22 := RD.genMload r21 (by native_decide) (by evm_ov)
    have r23 := r22.swap1 (by native_decide) (by evm_ov)
    have r24 := r23.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
    have r25 := r24.jump (by native_decide) (by jump_dest) (by evm_ov)
    have ha25 := memoryFundingAt (credit := credit) r25 (by memory_fund ha18)
    exact Or.inr ⟨hp, _, _, ha25, r25⟩
  · have hp' := Bool.eq_false_of_not_eq_true hp
    exact Or.inl ⟨hp', r13.sstoreStatic hp' (by native_decide) (by evm_ov)⟩

end Benchmarks.Midnight
