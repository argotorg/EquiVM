import Benchmarks.Midnight.CheckedArithmetic

/-! Unsigned modulo and the compiler's checked modulo routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: EVM MOD agrees with natural-number remainder for a nonzero divisor.
theorem mod_toNat_of_ne (a b : UInt256) (hb : b ≠ ⟨0⟩) :
    (UInt256.mod a b).toNat = a.toNat % b.toNat := by
  unfold UInt256.mod
  rw [if_neg]
  · rfl
  · intro h
    apply hb
    have hv : b.val = 0 := beq_iff_eq.mp h
    cases b
    cases hv
    rfl

theorem mod_eq_zero_iff (a b : UInt256) (hb : b ≠ ⟨0⟩) :
    UInt256.mod a b = ⟨0⟩ ↔ a.toNat % b.toNat = 0 := by
  constructor
  · intro h
    rw [← mod_toNat_of_ne a b hb, h]
    rfl
  · intro h
    apply uint256_toNat_eq_zero
    rw [mod_toNat_of_ne a b hb, h]

theorem midnightCheckedMod {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hb : b ≠ ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨20085⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ret (UInt256.mod a b :: R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_20085_fallthrough
    (by simp; omega) (isZero_eq_zero_of_ne hb) rd
  have rd2 := midnightBlocks.midnight_block_20092 (by simp; omega) hret rd1
  exact ⟨_, _, rd2⟩

end Benchmarks.Midnight
