import Benchmarks.CompoundIII.Comet.AbsorbCalldata
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: solc's address-array end pointer, with nonwrapping uint64 inputs.
theorem uadd_shift5_add36_toNat (off len : UInt256)
    (hoff : off.toNat ≤ solcMaxU64) (hlen : len.toNat ≤ solcMaxU64) :
    ((off + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 36).toNat =
      off.toNat + 32 * len.toNat + 36 := by
  have hoff' : off.toNat < 2^64 := by change off.toNat ≤ 2^64 - 1 at hoff; omega
  have hlen' : len.toNat < 2^64 := by change len.toNat ≤ 2^64 - 1 at hlen; omega
  have hshiftBound : 32 * len.toNat < UInt256.size := by change _ < 2^256; omega
  have hshift : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat = 32 * len.toNat := by
    conv_lhs => rw [← u256_ofNat_toNat len]
    change ((UInt256.ofNat len.toNat).shiftLeft ⟨5⟩).toNat = _
    rw [shiftLeft5_ofNat_eq hshiftBound, UInt256.toNat_ofNat_of_lt hshiftBound]
  have hsum : (off + UInt256.shiftLeft len (UInt256.ofNat 5)).toNat =
      off.toNat + 32 * len.toNat := by
    rw [uadd_toNat, hshift, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
  rw [uadd_word_ofNat_toNat _ 36 (by rw [hsum]; change _ < 2^256; omega), hsum]

theorem absorb_offset_add35_toNat {off : UInt256} (hoff : off.toNat ≤ solcMaxU64) :
    (off + UInt256.ofNat 35).toNat = off.toNat + 35 := by
  apply uadd_word_ofNat_toNat off 35
  change _ < 2^256
  change off.toNat ≤ 2^64 - 1 at hoff
  omega

theorem absorb_offset_add35_small {off : UInt256} (hoff : off.toNat ≤ solcMaxU64) :
    (off + UInt256.ofNat 35).toNat < 2^255 := by
  rw [absorb_offset_add35_toNat hoff]
  change off.toNat ≤ 2^64 - 1 at hoff
  omega

end Benchmarks.CompoundIII.Comet
