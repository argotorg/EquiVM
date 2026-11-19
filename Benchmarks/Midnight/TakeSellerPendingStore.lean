import Benchmarks.Midnight.TakeBuyerDebtWrite

/-! The seller pending-fee store preserves the other live trade values. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES block 12437 with normalized storage and retained cumulative cost.
theorem midnightTakeSellerPendingStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret w0 w1 w2 w3 w4 slot : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hperm : I.perm = true) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨12437⟩
      ([value, ret, w0, w1, w2, w3, w4, slot] ++ R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret
      ([w0, w1, w2, w3, w4, slot] ++ R) mem aw rdata
      (storeHigh128Accounts σ I slot value) k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.not (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.or (by native_decide) (by evm_ov)
  have r23 := r22.dup8 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc24, r24⟩ := sstoreMono r23 hperm (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hret (by evm_ov)
  simp only [uint128Mask_computed, u256_land_comm (UInt256.lnot uint128Mask),
    shiftLeft128_highMask, u256_land_comm uint128Mask,
    u256_lor_comm (UInt256.shiftLeft _ _)] at r25
  exact ⟨_, _, by omega, r25⟩

end Benchmarks.Midnight
