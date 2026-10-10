import Benchmarks.Morpho.MetaMorphoV1_1.PackedStorage

/-! The validated short and long Solidity storage-string header encodings. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def storageStringLength (header : UInt256) : UInt256 :=
  if UInt256.land header ⟨1⟩ = ⟨0⟩ then UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩
  else UInt256.div header ⟨2⟩

def storageStringValid (header : UInt256) : Prop :=
  UInt256.land header ⟨1⟩ ≠ UInt256.lt (storageStringLength header) ⟨32⟩

instance (header : UInt256) : Decidable (storageStringValid header) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem storageStringDecode (header : UInt256) (hvalid : storageStringValid header) :
    solidityDecodeBytesLengthHeader header = .ok (storageStringLength header).toNat := by
  change (if UInt256.sub (UInt256.land header ⟨1⟩)
    (UInt256.lt (storageStringLength header) ⟨32⟩) = ⟨0⟩ then StorageReadResult.revert
    else StorageReadResult.ok (storageStringLength header).toNat) = _
  rw [if_neg (u256_sub_ne_zero_of_ne hvalid)]

theorem storageStringDecodeRevert (header : UInt256) (hbad : ¬ storageStringValid header) :
    solidityDecodeBytesLengthHeader header = .revert := by
  have he : UInt256.land header ⟨1⟩ = UInt256.lt (storageStringLength header) ⟨32⟩ :=
    Classical.not_not.mp hbad
  change (if UInt256.sub (UInt256.land header ⟨1⟩)
    (UInt256.lt (storageStringLength header) ⟨32⟩) = ⟨0⟩ then StorageReadResult.revert
    else StorageReadResult.ok (storageStringLength header).toNat) = _
  rw [he, u256_sub_self, if_pos rfl]

theorem storageStringLength_lt (header : UInt256) :
    (storageStringLength header).toNat < 2 ^ 255 := by
  have hh : header.toNat < 2 ^ 256 := header.val.isLt
  unfold storageStringLength
  split
  · rw [uland_toNat, udiv_toNat]
    have hm : Nat.land (header.toNat / 2) 127 ≤ header.toNat / 2 := Nat.and_le_left
    change Nat.land (header.toNat / 2) 127 < 2 ^ 255
    omega
  · rw [udiv_toNat]
    change header.toNat / 2 < 2 ^ 255
    omega

theorem storageStringShortLength (header : UInt256) (hvalid : storageStringValid header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩) :
    (storageStringLength header).toNat < 32 := by
  apply solidityShortBytesValid_lt32
  apply u256_sub_ne_zero_of_ne
  simpa only [storageStringValid, hflag] using hvalid

theorem storageStringLongLength (header : UInt256) (hvalid : storageStringValid header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩) :
    32 ≤ (storageStringLength header).toNat := by
  have hf := land_one_eq_one_of_ne_zero hflag
  by_contra hn
  have hc := ult_one (show (storageStringLength header).toNat < (⟨32⟩ : UInt256).toNat
    from Nat.lt_of_not_ge hn)
  exact hvalid (hf.trans hc.symm)

end Benchmarks.Morpho.MetaMorphoV1_1
