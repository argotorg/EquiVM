import Benchmarks.Midnight.TakeBuyerDebtWrite

variable {fork : Ethereum.Fork}

/-! Reading and writing the seller's credit after the pending-fee update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 12482 with a normalized read and cumulative cost bound.
theorem midnightTakeSellerCreditBalanceRead {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret w0 w1 w2 w3 w4 slot : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨12482⟩
      ([value, ret, uint128Mask, w0, w1, w2, w3, w4, slot] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨19743⟩
      ([low128 (solcSlotWordAt slot σ I), value, ret, uint128Mask, w0, w1, w2, w3, w4, slot] ++ R)
      mem aw rdata σ k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc4, r4⟩ := RD.sloadMono r3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, r7⟩

-- GENERALIZES block 12491 with normalized packed storage and retained cumulative cost.
theorem midnightTakeSellerCreditStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value w0 w1 w2 w3 slot : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g s0 ⟨12491⟩
      ([value, uint128Mask, w0, w1, w2, w3, uint128Mask, slot] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ⟨23403⟩
      ([w0, w1, w2, w3, uint128Mask, slot] ++ R) mem aw rdata
      (storeLow128Accounts σ I slot value) k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.and (by native_decide) (by evm_ov)
  have r3 := r2.dup6 (by native_decide) (by evm_ov)
  have r4 := r3.not (by native_decide) (by evm_ov)
  have r5 := r4.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc6, r6⟩ := RD.sloadMono r5 (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.or (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc10, r10⟩ := sstoreMono r9 hperm (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, r12⟩

end Benchmarks.Midnight
