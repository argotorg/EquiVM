import Benchmarks.CompoundIII.Comet.NegativePrincipal
import Benchmarks.CompoundIII.Comet.SignedWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: sign extension preserves the signed interpretation of a packed field.
theorem signedWord_signextend104 (w : UInt256) :
    signedWord (UInt256.signextend (UInt256.ofNat 12) w) = signed104 w := by
  rw [signed104_bitvec, signedWord]
  change (⟨(UInt256.signextend ⟨12⟩ ⟨w.val⟩).val⟩ : BitVec 256).toInt = _
  rw [signextend104_bitvec (⟨w.val⟩ : BitVec 256)]
  exact BitVec.toInt_signExtend_of_le (by decide)

-- LIBRARY CANDIDATE: a bounded negative magnitude has the expected signed packed value.
theorem signed104_zeroSub {w : UInt256} (hw : w.toNat ≤ 2^103) :
    signed104 (UInt256.sub (UInt256.ofNat 0) w) = -Int.ofNat w.toNat := by
  by_cases hz : w.toNat = 0
  · have he := uint256_toNat_eq_zero hz
    subst w
    decide
  · have hp : (UInt256.ofNat 0).toNat < w.toNat := by change 0 < w.toNat; omega
    rw [signed104_bitvec, BitVec.toInt_eq_toNat_cond]
    change (if 2 * ((UInt256.sub (UInt256.ofNat 0) w).toNat % 2^104) < 2^104 then
      Int.ofNat ((UInt256.sub (UInt256.ofNat 0) w).toNat % 2^104) else
      Int.ofNat ((UInt256.sub (UInt256.ofNat 0) w).toNat % 2^104) - Int.ofNat (2^104)) = _
    simp only [usub_toNat_underflow hp]
    change (if 2 * ((2^256 - w.toNat) % 2^104) < 2^104 then
      Int.ofNat ((2^256 - w.toNat) % 2^104) else
      Int.ofNat ((2^256 - w.toNat) % 2^104) - Int.ofNat (2^104)) = _
    have hm : (2^256 - w.toNat) % 2^104 = 2^104 - w.toNat := by omega
    rw [hm, if_neg (by omega)]
    simp only [Int.ofNat_eq_natCast]
    omega

theorem signextend104_zeroSub {w : UInt256} (hw : w.toNat ≤ 2^103) :
    UInt256.signextend (UInt256.ofNat 12) (UInt256.sub (UInt256.ofNat 0) w) =
      UInt256.sub (UInt256.ofNat 0) w := by
  change UInt256.signextend ⟨12⟩ _ = _
  rw [← signed104_word, signed104_zeroSub hw, wordOfInt_neg_natCast_eq_sub_zero]
  rfl

end Benchmarks.CompoundIII.Comet
