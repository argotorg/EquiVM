import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open scoped Fin.CommRing
namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES the constant-zero complement addition lemma to arbitrary words.
theorem wordAdd_lnot_eq_sub_addOne (a b : UInt256) :
    a + UInt256.lnot b = UInt256.sub a (b + ⟨1⟩) := by
  apply congrArg UInt256.mk
  change a.val + ((UInt256.ofNat (UInt256.size - 1)).val - b.val) = a.val - (b.val + 1)
  rw [show (UInt256.ofNat (UInt256.size - 1)).val = (-1 : Fin UInt256.size) by decide]
  ring

-- LIBRARY CANDIDATE: EVMLean's two complement implementations coincide.
theorem wordComplement_eq_lnot (word : UInt256) : UInt256.complement word = UInt256.lnot word := by
  apply congrArg UInt256.mk
  change 0 - (word.val + 1) = (UInt256.ofNat (UInt256.size - 1)).val - word.val
  rw [show (UInt256.ofNat (UInt256.size - 1)).val = (-1 : Fin UInt256.size) by decide]
  ring

theorem signedWordInt_eq (word : UInt256) :
    signedWordInt word = if word.toNat < 2 ^ 255 then Int.ofNat word.toNat
      else Int.ofNat word.toNat - 2 ^ 256 := by
  have hw : word.toNat < 2 ^ 256 := word.val.isLt
  have hm : Int.ofNat word.toNat % Int.ofNat (EVM.twoPow 256) = Int.ofNat word.toNat := by
    apply Int.emod_eq_of_lt (Int.natCast_nonneg _)
    exact Int.ofNat_lt.mpr hw
  simp only [signedWordInt, normalizeInt, hm]
  have hlt : Int.ofNat word.toNat < Int.ofNat (EVM.twoPow (256 - 1)) ↔ word.toNat < 2 ^ 255 :=
    Int.ofNat_lt
  simp only [hlt]
  rfl

theorem signedWordInt_of_lt (word : UInt256) (hw : word.toNat < 2 ^ 255) :
    signedWordInt word = Int.ofNat word.toNat := by
  rw [signedWordInt_eq, if_pos hw]

theorem signedWordInt_lnot (word : UInt256) :
    signedWordInt (UInt256.lnot word) = -1 - signedWordInt word := by
  have hw : word.toNat < 2 ^ 256 := word.val.isLt
  rw [signedWordInt_eq, signedWordInt_eq, lnot_toNat_gen]
  simp only [Int.ofNat_eq_natCast]
  by_cases h : word.toNat < 2 ^ 255
  · rw [if_pos h, if_neg (by omega)]
    omega
  · rw [if_neg h, if_pos (by omega)]
    omega

end Benchmarks.UniswapV3.Pool
