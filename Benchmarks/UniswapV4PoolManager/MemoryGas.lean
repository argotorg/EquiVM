import Benchmarks.UniswapV4PoolManager.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: memory expansion preserves its natural word count and is monotone.
theorem memoryWords_toNat (aw off len : UInt256) :
    (M aw off len).toNat = MachineState.M aw.toNat off.toNat len.toNat :=
  UInt256.toNat_ofNat_of_lt (MachineState.M_lt_uint256_size aw.val.isLt off.val.isLt len.val.isLt)

theorem memoryWords_ge_active (aw off len : UInt256) :
    aw.toNat ≤ (M aw off len).toNat := by
  rw [memoryWords_toNat]
  exact MachineState.M_ge_active _ _ _

theorem memoryWords_ge_span (aw off len : UInt256) (hpos : len.toNat ≠ 0) :
    (off.toNat+len.toNat+31)/32 ≤ (M aw off len).toNat := by
  rw [memoryWords_toNat]
  unfold MachineState.M
  cases he : len.toNat with
  | zero => exact (hpos he).elim
  | succ n => exact Nat.le_max_right _ _

theorem memoryCost_mono {a b : UInt256} (h : a.toNat ≤ b.toNat) : Cₘ a ≤ Cₘ b := by
  have hm := Cₘ_monotone_of_lt h b.val.isLt
  simpa only [u256_ofNat_toNat] using hm

-- LIBRARY CANDIDATE: a bounded active memory stays bounded for an access within its span.
theorem memoryWords_le {aw off len : UInt256} {bound : Nat}
    (ha : aw.toNat ≤ bound) (hs : off.toNat+len.toNat ≤ 32*bound) :
    (M aw off len).toNat ≤ bound := by
  rw [memoryWords_toNat]
  unfold MachineState.M
  split
  · exact ha
  · apply max_le ha
    omega

-- LIBRARY CANDIDATE: an access wholly inside active memory does not expand it.
theorem memoryWords_eq_self {aw off len : UInt256}
    (h : off.toNat+len.toNat ≤ aw.toNat*32) : M aw off len = aw := by
  rw [M, MachineState_M_eq_of_cover _ _ _ h, u256_ofNat_toNat]

theorem memoryWords_idem (aw off len : UInt256) : M (M aw off len) off len = M aw off len := by
  by_cases hz : len.toNat = 0
  · simp only [M, MachineState.M, hz, ite_true, u256_ofNat_toNat]
  · apply memoryWords_eq_self
    have hs := memoryWords_ge_span aw off len hz
    omega

end Benchmarks.UniswapV4PoolManager
