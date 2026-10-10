import Benchmarks.CompoundIII.Comet.TypedBits
import Benchmarks.CompoundIII.Comet.UintCastWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: typed OR on canonical unsigned operands at any Solidity width.
theorem evalUintOrNat (width : BitWidth) (x y : Nat)
    (hx : x < 2^width.val) (hy : y < 2^width.val) :
    evalIntBitwise (.uint width) Nat.lor (Int.ofNat x) (Int.ofNat y) =
      .int (Int.ofNat (Nat.lor x y)) := by
  have hnorm (z : Nat) (hz : z < 2^width.val) :
      normalizeInt (.uint width) (Int.ofNat z) = Int.ofNat z :=
    normalizeInt_uint_eq_self _ _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hz)
  unfold evalIntBitwise
  dsimp only [IntType.bitWidth]
  rw [hnorm x hx, hnorm y hy]
  exact congrArg Value.int (hnorm _ (nat_lor_lt_two_pow hx hy))

-- LIBRARY CANDIDATE: unsigned complement within the selected width.
theorem evalUintNotNat (width : BitWidth) (x : Nat) (hx : x < 2^width.val) :
    evalUnaryOp? (.bitNot (.uint width)) (.int (Int.ofNat x)) =
      some (.int (Int.ofNat (2^width.val - 1 - x))) := by
  have hp : 0 < 2^width.val := by positivity
  simp only [evalUnaryOp?, IntType.bitWidth, EVM.twoPow, Int.ofNat_eq_natCast,
    normalizeInt_uint_eq_self width _ (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hx),
    Int.toNat_natCast]
  rw [normalizeInt_uint_eq_self width _ (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr (show 2^width.val - 1 - x < 2^width.val by omega))]

-- LIBRARY CANDIDATE: truncating a word complement agrees with unsigned typed complement.
theorem uintCastWord_not_nat (width : BitWidth) (word : UInt256)
    (hw : word.toNat < 2^width.val) :
    (uintCastWord width (UInt256.lnot word)).toNat = 2^width.val - 1 - word.toNat := by
  rw [uintCastWord_nat, lnot_toNat_gen]
  have hm : (2^256 - 1) % 2^width.val = 2^width.val - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < width.val
    · simp only [decide_eq_true hi,
        decide_eq_true (show i < 256 by have := width.property.2.1; omega), Bool.true_and]
    · simp only [decide_eq_false hi, Bool.false_and]
  rw [← Nat.mod_sub_of_le (a := 2^256 - 1) (n := 2^width.val)
    (b := word.toNat) (by rw [hm]; omega), hm]

def typedBitUpdateWord (add : Bool) (width : BitWidth) (old : UInt256) (bit : Nat) : UInt256 :=
  let mask := UInt256.ofNat (2^bit)
  if add then UInt256.lor old mask else UInt256.land old (uintCastWord width (UInt256.lnot mask))

def typedBitUpdateExpr (add : Bool) (width : BitWidth) (value bit : Expr) : Expr :=
  let mask := .binary (.shl (.uint width))
    (.cast (.intLit 1) (.elem (.int (.uint width)))) bit
  .binary (if add then .bitOr (.uint width) else .bitAnd (.uint width)) value
    (if add then mask else .unary (.bitNot (.uint width)) mask)

-- LIBRARY CANDIDATE: set or clear a bit in a canonical unsigned word.
theorem typedBitUpdate_source {cfg frame evm valueExpr bitExpr} (add : Bool)
    (width : BitWidth) (value : UInt256) (bit : Nat)
    (hv : value.toNat < 2^width.val) (hb : bit < width.val)
    (he : evalExpr? cfg frame evm valueExpr = .ok (.int value.toNat))
    (hbit : evalExpr? cfg frame evm bitExpr = .ok (.int (Int.ofNat bit))) :
    evalExpr? cfg frame evm (typedBitUpdateExpr add width valueExpr bitExpr) =
      .ok (.int (typedBitUpdateWord add width value bit).toNat) := by
  have hm := evalUintBitMask width bit hb hbit
  have hp : 2^bit < 2^width.val := Nat.pow_lt_pow_right (by decide) hb
  have hp256 : 2^bit < UInt256.size := lt_of_lt_of_le hp
    (Nat.pow_le_pow_right (by decide) width.property.2.1)
  have hn : (UInt256.ofNat (2^bit)).toNat = 2^bit := UInt256.toNat_ofNat_of_lt hp256
  cases add
  · have hc : evalExpr? cfg frame evm
        (.unary (.bitNot (.uint width)) (.binary (.shl (.uint width))
          (.cast (.intLit 1) (.elem (.int (.uint width)))) bitExpr)) =
        .ok (.int (Int.ofNat (2^width.val - 1 - 2^bit))) := by
      simp only [evalExpr?, hm, bind, EvalResult.bind, evalUintNotNat width _ hp,
        EvalResult.ofOption]
    have hw := uintCastWord_not_nat width (UInt256.ofNat (2^bit)) (by rw [hn]; exact hp)
    have hcBound : 2^width.val - 1 - 2^bit < 2^width.val := by omega
    simp only [typedBitUpdateExpr, Bool.false_eq_true, if_false, evalExpr?, he, hc,
      bind, EvalResult.bind, evalBinaryOp?, typedBitUpdateWord, uland_toNat, hw, hn]
    exact congrArg EvalResult.ok (evalUintAndNat width _ _ hv hcBound)
  · simp only [typedBitUpdateExpr, if_true, evalExpr?, he, hm, bind, EvalResult.bind,
      evalBinaryOp?, typedBitUpdateWord, u256_lor_toNat_exact, hn]
    exact congrArg EvalResult.ok (evalUintOrNat width _ _ hv hp)

end Benchmarks.CompoundIII.Comet
