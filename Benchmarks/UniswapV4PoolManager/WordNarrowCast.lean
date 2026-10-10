import Benchmarks.UniswapV4PoolManager.WordSignedCast
import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a signed cast preserves the residue at its own width.
theorem normalizeSignedResidue (bits : BitWidth) (x : Int) :
    normalizeInt (.sint bits) x % Int.ofNat (2^bits.val) = x % Int.ofNat (2^bits.val) := by
  simp only [normalizeInt, EVM.twoPow]
  split
  · exact Int.emod_emod _ _
  · simp only [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod]

-- LIBRARY CANDIDATE: signed normalization depends only on the residue.
theorem normalizeSignedCongr (bits : BitWidth) {x y : Int}
    (h : x % Int.ofNat (2^bits.val) = y % Int.ofNat (2^bits.val)) :
    normalizeInt (.sint bits) x = normalizeInt (.sint bits) y := by
  simp only [normalizeInt, EVM.twoPow, h]

-- LIBRARY CANDIDATE: signed truncation before addition can be deferred to the result.
theorem normalizeSignedAddLeft (bits : BitWidth) (x y : Int) :
    normalizeInt (.sint bits) (normalizeInt (.sint bits) x+y) = normalizeInt (.sint bits) (x+y) := by
  apply normalizeSignedCongr
  calc
    _ = (normalizeInt (.sint bits) x % Int.ofNat (2^bits.val) + y % Int.ofNat (2^bits.val)) %
        Int.ofNat (2^bits.val) := Int.add_emod _ _ _
    _ = (x % Int.ofNat (2^bits.val) + y % Int.ofNat (2^bits.val)) % Int.ofNat (2^bits.val) := by
      rw [normalizeSignedResidue]
    _ = _ := (Int.add_emod _ _ _).symm

-- LIBRARY CANDIDATE: signed truncation before subtraction can be deferred to the result.
theorem normalizeSignedSubLeft (bits : BitWidth) (x y : Int) :
    normalizeInt (.sint bits) (normalizeInt (.sint bits) x-y) = normalizeInt (.sint bits) (x-y) := by
  simpa only [sub_eq_add_neg] using normalizeSignedAddLeft bits x (-y)

-- GENERALIZES normalizeUintAfterSigned to an unsigned cast narrower than the signed cast.
theorem normalizeUintAfterSignedWidth (lo hi : BitWidth) (hwidth : lo.val ≤ hi.val) (x : Int) :
    normalizeInt (.uint lo) (normalizeInt (.sint hi) x) = normalizeInt (.uint lo) x := by
  have hd : Int.ofNat (2^lo.val) ∣ Int.ofNat (2^hi.val) := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int] using pow_dvd_pow (2 : Int) hwidth
  change normalizeInt (.sint hi) x % Int.ofNat (2^lo.val) = x % Int.ofNat (2^lo.val)
  calc
    _ = (normalizeInt (.sint hi) x % Int.ofNat (2^hi.val)) % Int.ofNat (2^lo.val) :=
      (Int.emod_emod_of_dvd _ hd).symm
    _ = (x % Int.ofNat (2^hi.val)) % Int.ofNat (2^lo.val) := by rw [normalizeSignedResidue]
    _ = _ := Int.emod_emod_of_dvd _ hd

theorem signextend24_add_left (a b : UInt256) :
    UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) a+b) =
      UInt256.signextend (UInt256.ofNat 2) (a+b) := by
  have hleft := normalizeSigned24Integer (EVM.signed (UInt256.signextend (UInt256.ofNat 2) a)+EVM.signed b)
  have hright := normalizeSigned24Integer (EVM.signed a+EVM.signed b)
  rw [wordOfInt_signed_add, ← normalizeSigned24Word, normalizeSignedAddLeft] at hleft
  rw [wordOfInt_signed_add] at hright
  have he := congrArg EVM.wordOfInt (hleft.symm.trans hright)
  simpa only [wordOfInt_signed] using he

theorem signextend24_sub_left (a b : UInt256) :
    UInt256.signextend (UInt256.ofNat 2) (UInt256.sub (UInt256.signextend (UInt256.ofNat 2) a) b) =
      UInt256.signextend (UInt256.ofNat 2) (UInt256.sub a b) := by
  have hleft := normalizeSigned24Integer (EVM.signed (UInt256.signextend (UInt256.ofNat 2) a)-EVM.signed b)
  have hright := normalizeSigned24Integer (EVM.signed a-EVM.signed b)
  rw [wordOfInt_signed_sub, ← normalizeSigned24Word, normalizeSignedSubLeft] at hleft
  rw [wordOfInt_signed_sub] at hright
  have he := congrArg EVM.wordOfInt (hleft.symm.trans hright)
  simpa only [wordOfInt_signed] using he

theorem signextend24_lowByte (w : UInt256) :
    UInt256.land (UInt256.signextend (UInt256.ofNat 2) w) (UInt256.ofNat 255) =
      UInt256.land w (UInt256.ofNat 255) := by
  apply u256_inj
  apply Int.ofNat_inj.mp
  change Int.ofNat (UInt256.land (UInt256.signextend (UInt256.ofNat 2) w) (UInt256.ofNat 255)).toNat =
    Int.ofNat (UInt256.land w (UInt256.ofNat 255)).toNat
  rw [← normalizeUintSignedWord ⟨8, by decide⟩ _ (UInt256.ofNat 255) rfl,
    ← normalizeUintSignedWord ⟨8, by decide⟩ _ (UInt256.ofNat 255) rfl,
    ← normalizeSigned24Word, normalizeUintAfterSignedWidth ⟨8, by decide⟩ ⟨24, by decide⟩ (by decide)]

theorem signextend24_idempotent (w : UInt256) :
    UInt256.signextend (UInt256.ofNat 2) (UInt256.signextend (UInt256.ofNat 2) w) =
      UInt256.signextend (UInt256.ofNat 2) w :=
  (signextend24_eq_iff _).mpr (signextend24_canonical _)

end Benchmarks.UniswapV4PoolManager
