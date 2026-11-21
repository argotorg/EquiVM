import Benchmarks.Midnight.Allocation

/-! Arithmetic conditions for the runtime's bounded memory allocator. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem allocationCheck_ok {ptr next : UInt256}
    (hnext : next.toNat < 2 ^ 64) (hle : ptr.toNat ≤ next.toNat) :
    allocationCheck ptr next = ⟨0⟩ := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  rw [allocationCheck, hmask, ugt_zero (by change next.toNat ≤ 18446744073709551615; omega),
    ult_zero hle]
  rfl

theorem allocationCheck_large {ptr next : UInt256}
    (hnext : 2^64 ≤ next.toNat) (hle : ptr.toNat ≤ next.toNat) :
    allocationCheck ptr next ≠ ⟨0⟩ := by
  have hg : UInt256.gt next
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨1⟩ := by
    apply ugt_one
    change 18446744073709551615 < next.toNat
    omega
  rw [allocationCheck, hg, ult_zero hle]
  decide

theorem allocationEnd_toNat {ptr size : UInt256}
    (hs : size.toNat + 31 < UInt256.size)
    (hp : ptr.toNat + (size.toNat + 31) / 32 * 32 < UInt256.size) :
    (allocationEnd ptr size).toNat = ptr.toNat + (size.toNat + 31) / 32 * 32 := by
  have hr : (UInt256.land (size + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31))).toNat = (size.toNat + 31) / 32 * 32 := by
    change (UInt256.land (size + UInt256.ofNat 31) (UInt256.lnot ⟨31⟩)).toNat = _
    rw [longDataCutoff_toNat, uadd_word_ofNat_toNat size 31 hs]
  unfold allocationEnd
  rw [uadd_toNat, hr, Nat.mod_eq_of_lt hp]

theorem allocationCheck_bounded {ptr size : UInt256}
    (hs : size.toNat + 31 < UInt256.size)
    (hp : ptr.toNat + (size.toNat + 31) / 32 * 32 < 2 ^ 64) :
    allocationCheck ptr (allocationEnd ptr size) = ⟨0⟩ := by
  have he := allocationEnd_toNat (ptr := ptr) hs (by change _ < 2 ^ 256; omega)
  apply allocationCheck_ok
  · rw [he]; exact hp
  · rw [he]; omega

end Benchmarks.Midnight
