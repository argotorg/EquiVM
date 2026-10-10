import Benchmarks.UniswapV4PoolManager.WordOperationsSource
import Benchmarks.UniswapV4PoolManager.SignedArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: the unsigned residue of an encoded integer.
theorem wordOfIntResidue (i : Int) :
    Int.ofNat (EVM.wordOfInt i).toNat = i % (2^256 : Int) := by
  have hl := Int.emod_nonneg i (by decide : (2^256 : Int) ≠ 0)
  have hh := Int.emod_lt_of_pos i (by decide : (0 : Int) < 2^256)
  rw [wordOfInt_eq_mod]
  change Int.ofNat ((i % (2^256 : Int)).toNat % 2^256) = _
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg hl]

-- LIBRARY CANDIDATE: a signed-256 cast is the signed interpretation of its word encoding.
theorem normalizeSignedWordOfInt (i : Int) :
    normalizeInt (.sint ⟨256, by decide⟩) i = EVM.signed (EVM.wordOfInt i) := by
  have hn : normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat (EVM.wordOfInt i).toNat) =
      EVM.signed (EVM.wordOfInt i) := normalizeInt_sint256_word _
  rw [← hn]
  have h := wordOfIntResidue i
  simp only [normalizeInt]
  rw [h]
  change (if i % (2^256 : Int) < (2^255 : Int) then i % (2^256 : Int)
      else i % (2^256 : Int) - (2^256 : Int)) =
    (if (i % (2^256 : Int)) % (2^256 : Int) < (2^255 : Int) then (i % (2^256 : Int)) % (2^256 : Int)
      else (i % (2^256 : Int)) % (2^256 : Int) - (2^256 : Int))
  simp only [Int.emod_emod]

-- LIBRARY CANDIDATE: signed word multiplication encodes as EVM MUL.
theorem wordOfInt_signed_mul (x y : UInt256) :
    EVM.wordOfInt (EVM.signed x * EVM.signed y) = UInt256.mul x y := by
  have hx : EVM.signed x % (2^256 : Int) = Int.ofNat x.toNat := normalizeUnsignedSigned x
  have hy : EVM.signed y % (2^256 : Int) = Int.ofNat y.toNat := normalizeUnsignedSigned y
  apply u256_inj
  rw [wordOfInt_eq_mod, u256_mul_toNat]
  change ((EVM.signed x * EVM.signed y) % (2^256 : Int)).toNat % 2^256 = (x.toNat*y.toNat) % 2^256
  rw [Int.mul_emod, hx, hy]
  simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul]
  change ((Int.ofNat (x.toNat*y.toNat)) % Int.ofNat (2^256)).toNat % 2^256 = _
  simp only [Int.ofNat_eq_natCast, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_mod]

-- LIBRARY CANDIDATE: signed subtraction encodes as EVM SUB.
theorem wordOfInt_signed_sub (x y : UInt256) :
    EVM.wordOfInt (EVM.signed x - EVM.signed y) = UInt256.sub x y := by
  have hx : EVM.signed x % (2^256 : Int) = Int.ofNat x.toNat := normalizeUnsignedSigned x
  have hy : EVM.signed y % (2^256 : Int) = Int.ofNat y.toNat := normalizeUnsignedSigned y
  rw [← wordOfInt_sub_natCasts]
  rw [wordOfInt_eq_mod, wordOfInt_eq_mod]
  change UInt256.ofNat ((EVM.signed x - EVM.signed y) % (2^256 : Int)).toNat =
    UInt256.ofNat ((Int.ofNat x.toNat - Int.ofNat y.toNat) % (2^256 : Int)).toNat
  rw [Int.sub_emod, hx, hy]

-- LIBRARY CANDIDATE: shifting a signed integer and encoding it agrees with EVM SHL.
theorem wordOfInt_signed_shl (x : UInt256) {n : Nat} (hn : n < 256) :
    EVM.wordOfInt (EVM.signed x * Int.ofNat (2^n)) = UInt256.shiftLeft x (UInt256.ofNat n) := by
  have hx : EVM.signed x % (2^256 : Int) = Int.ofNat x.toNat := normalizeUnsignedSigned x
  have hp : (Int.ofNat (2^n)) % (2^256 : Int) = Int.ofNat (2^n) := by
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    exact Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide) hn)
  apply u256_inj
  rw [wordOfInt_eq_mod, wordShiftLeftNat x hn]
  change ((EVM.signed x * Int.ofNat (2^n)) % (2^256 : Int)).toNat % 2^256 = (x.toNat*2^n) % 2^256
  rw [Int.mul_emod, hx, hp]
  simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul]
  change ((Int.ofNat (x.toNat*2^n)) % Int.ofNat (2^256)).toNat % 2^256 = _
  simp only [Int.ofNat_eq_natCast, ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_mod]

end Benchmarks.UniswapV4PoolManager
