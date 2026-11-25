import Benchmarks.Midnight.TakeBuyerDebtWrite

variable {fork : Ethereum.Fork}

/-! Ordered buyer-credit storage blocks, retaining memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 12399 by retaining its cumulative gas bound.
theorem midnightTakeBuyerCreditRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret slot : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨12399⟩
      (value :: ret :: uint128Mask :: slot :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨20456⟩
      (low128 (solcSlotWordAt slot σ I) :: value :: ret :: uint128Mask :: slot :: R)
      mem aw rdata σ k' C' := by
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc4, r4⟩ := RD.sloadMono r3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 20456) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, r7⟩

-- GENERALIZES block 12408 with normalized packed storage and retained memory funding.
theorem midnightTakeBuyerCreditStore {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value buyerSlot sellerSlot w0 w1 w2 w3 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hperm : I.perm = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨12408⟩
      ([value, uint128Mask, buyerSlot, w0, w1, w2, w3, uint128Mask, sellerSlot] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', MemoryFunding credit mem (M aw (UInt256.ofNat 160) ⟨32⟩) C' ∧
      RD fork midnightBytecode I g s0 ⟨19743⟩
        ([UInt256.shiftRight (solcSlotWordAt sellerSlot
            (storeLow128Accounts σ I buyerSlot value) I) (UInt256.ofNat 128),
          memLoad (UInt256.ofNat 160) mem, ⟨12437⟩, ⟨12469⟩, w0, w1, w2, w3,
          uint128Mask, sellerSlot] ++ R)
        mem (M aw (UInt256.ofNat 160) ⟨32⟩) rdata
        (storeLow128Accounts σ I buyerSlot value) k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc6, r6⟩ := RD.sloadMono r5 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.or (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc10, r10⟩ := sstoreMono r9 hperm (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 12469) (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 12437) (by native_decide) (by evm_ov)
  have r13 := r12.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc14, r14⟩ := RD.sloadMono r13 (by native_decide) (by evm_ov)
  have ha14 := memoryFundingAt (credit := credit) r14 (ha.mono (by omega))
  have r15 := r14.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r16 := r15.shr (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := RD.genMload r17 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r21 := r20.jump (by native_decide) (by jump_dest) (by evm_ov)
  have ha21 := memoryFundingAt (credit := credit) r21 (by memory_fund ha14)
  exact ⟨_, _, ha21, r21⟩

end Benchmarks.Midnight
