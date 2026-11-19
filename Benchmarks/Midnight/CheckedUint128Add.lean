import Benchmarks.Midnight.CheckedUint128
import Benchmarks.Midnight.RuntimeBlocks_078
import Benchmarks.Midnight.RuntimeBlocks_087

/-! Checked addition and narrowing to uint128. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCheckedAdd128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2^128) (hb : b.toNat < 2^128) (hsum : a.toNat + b.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20456⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b (show a.toNat + b.toNat < UInt256.size from by
    change _ < 2^256; omega)
  have hc : UInt256.gt (a + b) uint128Mask = ⟨0⟩ := by
    apply ugt_zero
    rw [hn]
    change _ ≤ 340282366920938463463374607431768211455
    omega
  have rd1 := midnightBlocks.midnight_block_20456_fallthrough hstack
    (by rw [uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb]; exact hc) rd
  simp only [midnightBlocks.midnight_block_20456_fallthrough_stack,
    uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb] at rd1
  exact ⟨_, _, midnightBlocks.midnight_block_20487 (by simp only [List.length_cons]; omega) hret rd1⟩

theorem midnightCheckedAdd128Revert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2^128) (hb : b.toNat < 2^128) (hsum : 2^128 ≤ a.toNat + b.toNat)
    (rd : RD midnightBytecode I g s0 ⟨20456⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev midnightBytecode g s0 := by
  have hn : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b (show a.toNat + b.toNat < UInt256.size from by
    change _ < 2^256; omega)
  have hc : UInt256.gt (a + b) uint128Mask = ⟨1⟩ := by
    apply ugt_one
    rw [hn]
    change 340282366920938463463374607431768211455 < _
    omega
  have rd1 := midnightBlocks.midnight_block_20456_taken hstack
    (by rw [uint128Mask_computed, uint128Mask_clean ha, uint128Mask_clean hb];
        change UInt256.gt (a + b) uint128Mask ≠ _; rw [hc]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_7302 (by
    simp only [midnightBlocks.midnight_block_20456_taken_stack, List.length_cons]; omega) rd1

theorem midnightToUint128 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw value ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024) (hvalue : value.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨23403⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (value :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.gt value uint128Mask = ⟨0⟩ := by
    apply ugt_zero
    change value.toNat ≤ 340282366920938463463374607431768211455
    omega
  have rd1 := midnightBlocks.midnight_block_23403_fallthrough (by simp only [List.length_cons]; omega)
    (by rw [uint128Mask_computed]; exact hc) rd
  have rd2 := midnightBlocks.midnight_block_23418 hstack hret rd1
  simp only [midnightBlocks.midnight_block_23418_stack, uint128Mask_computed,
    u256_land_comm uint128Mask, uint128Mask_clean hvalue] at rd2
  exact ⟨_, _, rd2⟩

end Benchmarks.Midnight
