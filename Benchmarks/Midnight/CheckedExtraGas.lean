import Benchmarks.Midnight.CheckedUint128Add

/-! Checked division and uint128 addition preserve accumulated costs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem midnightCheckedDiv_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hnz : b ≠ ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨19391⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret (UInt256.div a b :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19391_fallthrough
    (by simp; omega) (isZero_eq_zero_of_ne hnz) rd
  have rd2 := midnightBlocks.midnight_block_19398 (by omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

theorem midnightCheckedAdd128_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (ha : a.toNat < 2^128) (hb : b.toNat < 2^128) (hsum : a.toNat + b.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20456⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
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
  have rd2 := midnightBlocks.midnight_block_20487
    (by simp only [List.length_cons]; omega) hret rd1
  exact ⟨_, _, by omega, rd2⟩

end Benchmarks.Midnight
