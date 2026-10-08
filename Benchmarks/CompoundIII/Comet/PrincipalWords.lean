import Benchmarks.CompoundIII.Comet.SignedFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem signed104_bounds (w : UInt256) :
    -(2^103 : Int) ≤ signed104 w ∧ signed104 w < (2^103 : Int) := by
  rw [signed104_bitvec]
  exact ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩

theorem signed104_mod (w : UInt256) :
    signed104 w % Int.ofNat EVM.wordModulus =
      Int.ofNat (UInt256.signextend ⟨12⟩ w).toNat := by
  rw [signed104_bitvec, ← BitVec.toInt_signExtend_of_le (v := 256) (by decide)]
  have hh := congrArg BitVec.toNat
    (BitVec.ofInt_toInt (x := ((⟨w.val⟩ : BitVec 256).setWidth 104 |>.signExtend 256)))
  simp only [BitVec.toNat_ofInt] at hh
  have hmod : 0 ≤ ((⟨w.val⟩ : BitVec 256).setWidth 104 |>.signExtend 256).toInt %
      (2^256 : Nat) := Int.emod_nonneg _ (by decide)
  have hi := congrArg Int.ofNat hh
  simp only [Int.ofNat_eq_natCast] at hi
  rw [Int.toNat_of_nonneg hmod] at hi
  change _ = Int.ofNat (UInt256.signextend ⟨12⟩ w).val.val
  rw [signextend104_bitvec (⟨w.val⟩ : BitVec 256)]
  exact hi

theorem signed104_sgt_pos {w : UInt256} (hp : 0 < signed104 w) :
    UInt256.sgt (UInt256.signextend ⟨12⟩ w) ⟨0⟩ ≠ ⟨0⟩ := by
  intro h
  have hb := signed104_bounds w
  have hn := int_nonpos_of_word_sgt_zero (by omega) (by omega) (signed104_mod w) h
  omega

theorem signed104_sgt_nonpos {w : UInt256} (hp : signed104 w ≤ 0) :
    UInt256.sgt (UInt256.signextend ⟨12⟩ w) ⟨0⟩ = ⟨0⟩ := by
  by_contra h
  have hb := signed104_bounds w
  have hn := int_pos_of_word_sgt_ne_zero (by omega) (by omega) (signed104_mod w) h
  omega

def positivePrincipal (w : UInt256) : UInt256 := UInt256.ofNat (signed104 w).toNat

theorem positivePrincipal_toNat (w : UInt256) :
    (positivePrincipal w).toNat = (signed104 w).toNat := by
  apply UInt256.toNat_ofNat_of_lt
  have hb := signed104_bounds w
  change (signed104 w).toNat < 2^256
  omega

theorem positivePrincipal_lt (w : UInt256) : (positivePrincipal w).toNat < 2^103 := by
  rw [positivePrincipal_toNat]
  have hb := signed104_bounds w
  omega

theorem positivePrincipal_int {w : UInt256} (hp : 0 ≤ signed104 w) :
    Int.ofNat (positivePrincipal w).toNat = signed104 w := by
  rw [positivePrincipal_toNat]
  exact Int.toNat_of_nonneg hp

theorem signextend104_nonneg {w : UInt256} (hp : 0 ≤ signed104 w) :
    UInt256.signextend ⟨12⟩ w = positivePrincipal w := by
  rw [← signed104_word, wordOfInt_nonneg _ hp]
  rfl

theorem signed104_low {w : UInt256} (hw : w.toNat < 2^103) :
    signed104 w = Int.ofNat w.toNat := by
  rw [signed104_bitvec, BitVec.toInt_eq_toNat_cond]
  have hb : w.toNat < 2^104 := lt_trans hw (by decide)
  change (if 2 * (w.toNat % 2^104) < 2^104 then Int.ofNat (w.toNat % 2^104)
    else Int.ofNat (w.toNat % 2^104) - Int.ofNat (2^104)) = _
  simp only [Nat.mod_eq_of_lt hb]
  rw [if_pos (by omega)]

theorem signextend104_low {w : UInt256} (hw : w.toNat < 2^103) :
    UInt256.signextend (UInt256.ofNat 12) w = w := by
  change UInt256.signextend ⟨12⟩ w = w
  rw [← signed104_word, signed104_low hw, wordOfInt_ofNat_toNat]

end Benchmarks.CompoundIII.Comet
