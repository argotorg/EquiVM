import Benchmarks.UniswapV4PoolManager.SignedArithmetic

/-! Canonical 24-bit ABI words used by fees and tick spacing. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

abbrev abiUInt24 : ABIType := .elem (.int (.uint ⟨24, by decide⟩))
abbrev abiInt24 : ABIType := .elem (.int (.sint ⟨24, by decide⟩))

-- LIBRARY CANDIDATE: masking tests unsigned canonicality at any width.
theorem landMask_eq_iff {bits : Nat} (word mask : UInt256)
    (hm : mask.toNat = 2^bits-1) :
    UInt256.land word mask = word ↔ word.toNat < EVM.twoPow bits := by
  constructor
  · intro h
    have hb := u256LandMaskToNatLtOfToNat word mask hm
    simpa only [h] using hb
  · exact u256LandMaskCleanOfToNat word mask hm

def int24Canonical (w : UInt256) : Prop := w.toNat < 2^23 ∨ 2^256-2^23 ≤ w.toNat
instance (w : UInt256) : Decidable (int24Canonical w) := inferInstanceAs (Decidable (_ ∨ _))

theorem signextend24_low (w : UInt256) (hw : w.toNat < 2^23) :
    UInt256.signextend ⟨2⟩ w = w := by
  change (if UInt256.land w ⟨2^23⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256-2^23⟩
    else UInt256.land w ⟨2^23-1⟩) = w
  have hz : UInt256.land w ⟨2^23⟩ = ⟨0⟩ := by
    apply u256_inj
    rw [uland_toNat]
    change w.toNat &&& 2^23 = 0
    rw [Nat.and_two_pow, Nat.testBit_eq_false_of_lt hw]
    rfl
  rw [if_neg (not_not.mpr hz)]
  exact u256LandMaskCleanOfToNat w ⟨2^23-1⟩ rfl hw

theorem signextend24_high (w : UInt256) (hw : 2^256-2^23 ≤ w.toNat) :
    UInt256.signextend ⟨2⟩ w = w := by
  have hlt : w.toNat < 2^256 := w.val.isLt
  have hdiv : w.toNat / 2^23 = 2^233-1 := by omega
  change (if UInt256.land w ⟨2^23⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256-2^23⟩
    else UInt256.land w ⟨2^23-1⟩) = w
  have hn : UInt256.land w ⟨2^23⟩ ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [uland_toNat] at he'
    change w.toNat &&& 2^23 = 0 at he'
    rw [Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq, hdiv] at he'
    norm_num at he'
  rw [if_pos hn]
  have hm : w.toNat &&& (2^256-2^23) = 2^256-2^23 := by
    have he := natLandClearLow w.toNat 23 (by decide) hlt
    change w.toNat &&& (2^256-2^23) = (w.toNat / 2^23)*2^23 at he
    rw [he, hdiv]
    decide
  have ho : w.toNat ||| (2^256-2^23) = w.toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n : Nat => n.testBit i) hm
    dsimp only at hi
    rw [Nat.testBit_and] at hi
    rw [Nat.testBit_or]
    cases h0 : w.toNat.testBit i <;> cases h1 : (2^256-2^23).testBit i <;> simp_all
  apply u256_inj
  change (w.toNat ||| (2^256-2^23)) % 2^256 = w.toNat
  rw [ho, Nat.mod_eq_of_lt hlt]

theorem signextend24_canonical (w : UInt256) :
    int24Canonical (UInt256.signextend ⟨2⟩ w) := by
  have hlt : w.toNat < 2^256 := w.val.isLt
  change int24Canonical (if UInt256.land w ⟨2^23⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256-2^23⟩
    else UInt256.land w ⟨2^23-1⟩)
  split
  · right
    have hb : w.toNat ||| (2^256-2^23) < 2^256 := Nat.or_lt_two_pow hlt (by decide)
    change 2^256-2^23 ≤ (w.toNat ||| (2^256-2^23)) % 2^256
    rw [Nat.mod_eq_of_lt hb]
    exact Nat.right_le_or
  · left
    exact u256LandMaskToNatLtOfToNat w ⟨2^23-1⟩ rfl

theorem signextend24_eq_iff (w : UInt256) :
    UInt256.signextend ⟨2⟩ w = w ↔ int24Canonical w := by
  constructor
  · intro h; simpa only [h] using signextend24_canonical w
  · rintro (hl | hh)
    · exact signextend24_low w hl
    · exact signextend24_high w hh

theorem decodeABIWord_uint24 (w : UInt256) :
    decodeABIWord? abiUInt24 w =
      if w.toNat < 2^24 then some (.int (Int.ofNat w.toNat)) else none := by
  simp only [decodeABIWord?, show ¬ (24:Nat) = 0 by decide, if_false]
  rfl

theorem decodeABIWord_int24 (w : UInt256) :
    decodeABIWord? abiInt24 w =
      if int24Canonical w then some (.int (EVM.signed w)) else none := by
  simp only [decodeABIWord?, EVM.signed, int24Canonical, UInt256.toNat,
    show ¬ (24:Nat) = 0 by decide, if_false, EVM.wordModulus, EVM.signBit, EVM.twoPow]
  generalize hn : (w.val : Nat) = n
  by_cases hl : n < 2^23
  · simp only [hl, true_or, if_true, show n < 2^255 by omega]
  · simp only [hl, false_or, if_false]
    by_cases hh : 2^256-2^23 ≤ n
    · simp only [hh, if_true, show ¬n < 2^255 by omega, if_false]
    · simp only [hh, if_false]

end Benchmarks.UniswapV4PoolManager
