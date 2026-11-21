import Benchmarks.Midnight.CheckedUint128Add
import Benchmarks.Midnight.RuntimeBlocks_018

/-! Checked uint128 helpers retaining the cost already paid by their caller. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCheckedSub128_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (ha : a.toNat < 2^128) (hb : b.toNat < 2^128)
    (hle : b.toNat ≤ a.toNat) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19743⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt (UInt256.sub a b) uint128Mask = ⟨0⟩ := by
    apply ugt_zero
    rw [usub_toNat hle]
    change _ ≤ 340282366920938463463374607431768211455
    omega
  have rd1 := midnightBlocks.midnight_block_19743_fallthrough hstack
    (by rw [uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb]; exact hc) rd
  simp only [midnightBlocks.midnight_block_19743_fallthrough_stack,
    uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb] at rd1
  have rd2 := midnightBlocks.midnight_block_19774 (by simp only [List.length_cons]; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

theorem midnightToUint128_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hvalue : value.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨23403⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret (value :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt value uint128Mask = ⟨0⟩ := by
    apply ugt_zero
    change value.toNat ≤ 340282366920938463463374607431768211455
    omega
  have rd1 := midnightBlocks.midnight_block_23403_fallthrough (by simp only [List.length_cons]; omega)
    (by rw [uint128Mask_computed]; exact hc) rd
  have rd2 := midnightBlocks.midnight_block_23418 hstack hret rd1
  simp only [midnightBlocks.midnight_block_23418_stack, uint128Mask_computed,
    u256_land_comm uint128Mask, uint128Mask_clean hvalue] at rd2
  exact ⟨_, _, by omega, rd2⟩

theorem midnightToUint128Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hvalue : 2^128 ≤ value.toNat)
    (rd : RD midnightBytecode I g s0 ⟨23403⟩ (value :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hc : UInt256.gt value uint128Mask = ⟨1⟩ := by
    apply ugt_one
    change 340282366920938463463374607431768211455 < value.toNat
    omega
  have rd1 := midnightBlocks.midnight_block_23403_taken
    (by simp only [List.length_cons]; omega)
    (by rw [uint128Mask_computed]; change UInt256.gt value uint128Mask ≠ _; rw [hc]; decide)
    (by jump_dest) rd
  exact midnightBlocks.midnight_block_23429 (by simp only [List.length_cons]; omega) rd1

theorem midnightReadLow128Sub {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw amount ret slot : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (rd : RD midnightBytecode I g s0 ⟨3993⟩ (amount :: ret :: uint128Mask :: slot :: R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨19743⟩
      (UInt256.land (solcSlotWordAt slot σ I) uint128Mask :: amount :: ret :: uint128Mask :: slot :: R)
      mem aw rdata σ k' C' := by
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.dup5 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hC, r4⟩ := RD.sloadMono r3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 19743) (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, r7⟩

end Benchmarks.Midnight
