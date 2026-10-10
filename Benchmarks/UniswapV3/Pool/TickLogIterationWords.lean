import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: compose word right shifts whose total count is below 256.
theorem wordShiftRight_add (word : UInt256) (a b : Nat) (hab : a + b < 256) :
    UInt256.shiftRight (UInt256.shiftRight word (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.shiftRight word (UInt256.ofNat (a + b)) := by
  have ha : (UInt256.ofNat a).toNat = a :=
    UInt256.toNat_ofNat_of_lt (by change a < 2 ^ 256; omega)
  have hb : (UInt256.ofNat b).toNat = b :=
    UInt256.toNat_ofNat_of_lt (by change b < 2 ^ 256; omega)
  have hs : (UInt256.ofNat (a + b)).toNat = a + b :=
    UInt256.toNat_ofNat_of_lt (lt_trans hab (by decide))
  apply u256_inj
  rw [wordShiftRight_toNat _ _ (by rw [hb]; omega),
    wordShiftRight_toNat _ _ (by rw [ha]; omega),
    wordShiftRight_toNat _ _ (by rw [hs]; exact hab), ha, hb, hs,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem wordShiftRight255_lt (word : UInt256) :
    (UInt256.shiftRight word ⟨255⟩).toNat < 2 := by
  rw [wordShiftRight_toNat _ _ (by decide)]
  have hw : word.toNat < 2 ^ 256 := word.val.isLt
  change word.toNat / 2 ^ 255 < 2
  omega

-- LIBRARY CANDIDATE: move a word's highest bit to a lower bit by masking a right shift.
theorem wordTopBit_maskShift (word : UInt256) (bits : Nat) (hbits : bits < 256) :
    UInt256.land (UInt256.ofNat (2 ^ bits))
      (UInt256.shiftRight word (UInt256.ofNat (255 - bits))) =
      UInt256.shiftLeft (UInt256.shiftRight word ⟨255⟩) (UInt256.ofNat bits) := by
  have hb : (UInt256.ofNat bits).toNat = bits :=
    UInt256.toNat_ofNat_of_lt (lt_trans hbits (by decide))
  have hs : (UInt256.ofNat (255 - bits)).toNat = 255 - bits :=
    UInt256.toNat_ofNat_of_lt (by change 255 - bits < 2 ^ 256; omega)
  have hp : 2 ^ bits < UInt256.size := Nat.pow_lt_pow_right (by decide) hbits
  have hq := wordShiftRight255_lt word
  have hfit : (UInt256.shiftRight word ⟨255⟩).toNat * 2 ^ bits < UInt256.size := by
    calc
      _ ≤ 1 * 2 ^ bits := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ bits := Nat.one_mul _
      _ < _ := hp
  apply u256_inj
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt hp,
    wordShiftRight_toNat _ _ (by rw [hs]; omega), hs,
    shiftLeft_toNat_of_noOverflow _ _ (by rw [hb]; exact hbits) (by rw [hb]; exact hfit), hb,
    wordShiftRight_toNat _ _ (by decide)]
  change 2 ^ bits &&& (word.toNat / 2 ^ (255 - bits)) = word.toNat / 2 ^ 255 * 2 ^ bits
  rw [Nat.two_pow_and, Nat.toNat_testBit, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 255 - bits + bits = 255 by omega]
  have hq' : word.toNat / 2 ^ 255 < 2 := by
    simpa only [wordShiftRight_toNat word ⟨255⟩ (by decide)] using hq
  rw [Nat.mod_eq_of_lt hq', Nat.mul_comm]

def tickLogSquare (r : UInt256) : UInt256 := UInt256.mul r r

def tickLogScaled (r : UInt256) : UInt256 := UInt256.shiftRight (tickLogSquare r) ⟨127⟩

def tickLogDigit (r : UInt256) : UInt256 := UInt256.shiftRight (tickLogScaled r) ⟨128⟩

def tickLogNext (r : UInt256) : UInt256 := UInt256.shiftRight (tickLogScaled r) (tickLogDigit r)

def tickLogAccumulate (log r : UInt256) (bits : Nat) : UInt256 :=
  UInt256.lor log (UInt256.shiftLeft (tickLogDigit r) (UInt256.ofNat bits))

def tickLogIteration (state : UInt256 × UInt256) (bits : Nat) : UInt256 × UInt256 :=
  (tickLogNext state.1, tickLogAccumulate state.2 state.1 bits)

theorem tickLogDigit_eq (r : UInt256) :
    tickLogDigit r = UInt256.shiftRight (tickLogSquare r) ⟨255⟩ :=
  wordShiftRight_add (tickLogSquare r) 127 128 (by decide)

theorem tickLogDigit_lt (r : UInt256) : (tickLogDigit r).toNat < 2 := by
  rw [tickLogDigit_eq]
  exact wordShiftRight255_lt _

theorem tickLogContribution_eq (r : UInt256) (bits : Nat) (hbits : bits < 256) :
    UInt256.land (UInt256.ofNat (2 ^ bits))
      (UInt256.shiftRight (tickLogSquare r) (UInt256.ofNat (255 - bits))) =
      UInt256.shiftLeft (tickLogDigit r) (UInt256.ofNat bits) := by
  rw [tickLogDigit_eq]
  exact wordTopBit_maskShift _ _ hbits

end Benchmarks.UniswapV3.Pool
