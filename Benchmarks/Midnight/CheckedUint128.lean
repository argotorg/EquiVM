import Benchmarks.Midnight.CheckedArithmetic
import Benchmarks.Midnight.PackedUint128
import Benchmarks.Midnight.PackedFields
import Benchmarks.Midnight.RuntimeBlocks_075

/-! Checked subtraction on canonical uint128 arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCheckedSub128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (ha : a.toNat < 2^128) (hb : b.toNat < 2^128)
    (hle : b.toNat ≤ a.toNat) (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19743⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
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
  exact ⟨_, _, rd2⟩

theorem midnightCheckedSub128Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (ha : a.toNat < 2^128) (hb : b.toNat < 2^128)
    (hlt : a.toNat < b.toNat)
    (rd : RD midnightBytecode I g s0 ⟨19743⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hc : UInt256.gt (UInt256.sub a b) uint128Mask = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hlt]
    change 340282366920938463463374607431768211455 < 2^256 + a.toNat - b.toNat
    omega
  have rd1 := midnightBlocks.midnight_block_19743_taken hstack
    (by rw [uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb];
        change UInt256.gt (UInt256.sub a b) uint128Mask ≠ _; rw [hc]; decide)
    (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302 (by
    simp only [midnightBlocks.midnight_block_19743_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
