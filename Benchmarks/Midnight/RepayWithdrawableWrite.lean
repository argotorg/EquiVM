import Benchmarks.Midnight.RepayPayerSource
import Benchmarks.Midnight.CollateralBlocksGas
import Benchmarks.Midnight.RuntimeBlocks_039
import Benchmarks.Midnight.RuntimeBlocks_040

/-! The withdrawable write and selection of the payer before the Repay event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightRepayWriteWithdrawable {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value slot dp id dl user : UInt256}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hperm : ee.perm = true)
    (h : RD midnightBytecode ee g s0 ⟨9992⟩
      (value :: uint128Mask :: slot :: dp :: id :: dl :: user :: UInt256.ofNat callback.val :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode ee g s0 ⟨10034⟩
      (repayHasCallback callback :: id :: dp :: UInt256.ofNat callback.val :: dl :: user ::
        UInt256.ofNat (repayPayer ee callback).val :: R)
      mem aw rdata (storeLow128Accounts σ ee slot value) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc3, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.or (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc15, r15⟩ := sstoreMono r14 hperm (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.dup6 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.dup1 (by native_decide) (by evm_ov)
  have r24 := r23.iszero (by native_decide) (by evm_ov)
  have r25 := r24.dup1 (by native_decide) (by evm_ov)
  have r26 := r25.iszero (by native_decide) (by evm_ov)
  have r27 := r26.swap7 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.swap4 (by native_decide) (by evm_ov)
  have r30 := r29.swap2 (by native_decide) (by evm_ov)
  have r31 := r30.swap1 (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 10352) (by native_decide) (by evm_ov)
  simp only [addressMask_computed, solcAddrMask_clean (addressWord_canonical callback)] at r32
  by_cases hz : callback = 0
  · have r33 := r32.jumpiT (by native_decide) (by simp [hz]; decide)
      (by jump_dest) (by evm_ov)
    have rr := midnightBlocks.midnight_block_10352
      (by omega) (by jump_dest) r33
    refine ⟨_, _, ?_, by
      simpa only [midnightBlocks.midnight_block_10352_stack, repayHasCallback, repayPayer,
        hz, if_true, show UInt256.ofNat (0 : AccountAddress).val = ⟨0⟩ from rfl,
        show UInt256.isZero ⟨0⟩ = ⟨1⟩ from rfl, show UInt256.isZero ⟨1⟩ = ⟨0⟩ from rfl,
        uint128Mask_computed, storeLow128Accounts, setUint128LowWord, u256_land_comm,
        u256_lor_comm] using rr⟩
    omega
  · have hn : UInt256.ofNat callback.val ≠ ⟨0⟩ := by
      intro he
      apply hz
      apply Fin.ext
      have hv := congrArg UInt256.toNat he
      change callback.val = 0
      simpa only [show (UInt256.ofNat callback.val).toNat = callback.val from
        addressWord_toNat_val callback] using hv
    have r33 := r32.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hn) (by evm_ov)
    have rr := midnightBlocks.midnight_block_10033
      (by omega) r33
    refine ⟨_, _, ?_, by
      simpa only [midnightBlocks.midnight_block_10033_stack, repayHasCallback, repayPayer,
        hz, if_false, isZero_eq_zero_of_ne hn, show UInt256.isZero ⟨0⟩ = ⟨1⟩ from rfl,
        uint128Mask_computed, storeLow128Accounts, setUint128LowWord, u256_land_comm,
        u256_lor_comm] using rr⟩
    omega

end Benchmarks.Midnight
