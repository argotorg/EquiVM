import Benchmarks.Midnight.TakeBuyerDebtWrite

/-! Seller debt storage and the following ordered market-balance read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 12505 with a normalized debt read and retained cumulative cost.
theorem midnightTakeSellerDebtRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret slot : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨12505⟩
      (value :: ⟨2⟩ :: ret :: uint128Mask :: slot :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨20456⟩
      (low128 (solcSlotWordAt (slot + ⟨2⟩) σ I) :: value :: ret :: uint128Mask ::
        (slot + ⟨2⟩) :: R) mem aw rdata σ k' C' := by
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.add (by native_decide) (by evm_ov)
  have r4 := r3.swap3 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc7, r7⟩ := RD.sloadMono r6 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, r10⟩

-- GENERALIZES block 12517 with normalized storage and retained cumulative cost.
theorem midnightTakeSellerDebtStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value slot marketSlot decrease ratifierPtr increase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD midnightBytecode I g s0 ⟨12517⟩
      ([value, uint128Mask, slot, marketSlot, decrease, ratifierPtr, increase] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨19536⟩
      ([low128 (solcSlotWordAt marketSlot (storeLow128Accounts σ I slot value) I),
        increase, ⟨12561⟩, decrease, ⟨4204⟩, ⟨12566⟩, uint128Mask, marketSlot,
        decrease, ratifierPtr, increase] ++ R) mem aw rdata
      (storeLow128Accounts σ I slot value) k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.not (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc10, r10⟩ := RD.sloadMono r9 (by native_decide) (by evm_ov)
  have r11 := r10.and (by native_decide) (by evm_ov)
  have r12 := r11.or (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := sstoreMono r13 hperm (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 12566) (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 4204) (by native_decide) (by evm_ov)
  have r22 := r21.dup5 (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 12561) (by native_decide) (by evm_ov)
  have r24 := r23.dup9 (by native_decide) (by evm_ov)
  have r25 := r24.dup6 (by native_decide) (by evm_ov)
  have r26 := r25.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc27, r27⟩ := RD.sloadMono r26 (by native_decide) (by evm_ov)
  have r28 := r27.and (by native_decide) (by evm_ov)
  have r29 := r28.push2 (UInt256.ofNat 19536) (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) (by jump_dest) (by evm_ov)
  simp only [uint128Mask_computed] at r30
  exact ⟨_, _, by omega, r30⟩

end Benchmarks.Midnight
