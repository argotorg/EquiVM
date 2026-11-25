import Benchmarks.Midnight.Common

/-! The twenty packed bytes of an address shifted into an MSTORE word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem addressWord_drop12_value (addr : AccountAddress) :
    fromBytesBigEndian ((EVM.word addr.val).toBytesBE.drop 12) = (EVM.word addr.val).toNat := by
  have hlen : (EVM.word addr.val).toBytesBE.length = 32 := word_toBytesBE_length_32 _
  have hjoin := fromBytesBigEndian_append ((EVM.word addr.val).toBytesBE.take 12)
    ((EVM.word addr.val).toBytesBE.drop 12)
  rw [List.take_append_drop, fromBytesBE_word, List.length_drop, hlen] at hjoin
  have hbound := fromBytesBigEndian_bound ((EVM.word addr.val).toBytesBE.drop 12)
  rw [List.length_drop, hlen] at hbound
  have hcanon : (EVM.word addr.val).toNat < 2^160 := addressWord_val_canonical addr
  norm_num only at hjoin hbound
  omega

theorem packedAddressBytes (addr : AccountAddress) :
    ((UInt256.shiftLeft (EVM.word addr.val) (UInt256.ofNat 96)).toByteArray.extract 0 20).toList =
      (EVM.word addr.val).toBytesBE.drop 12 := by
  apply fromBytesBigEndian_inj_of_length
  · rw [byteArray_toList_eq, Array.length_toList]
    change ((UInt256.shiftLeft (EVM.word addr.val) (UInt256.ofNat 96)).toByteArray.extract 0 20).size = _
    rw [ByteArray.size_extract, toByteArray_size, List.length_drop, word_toBytesBE_length_32]
    rfl
  · rw [bytesBE_extract_high _ 20 (by decide), addressWord_drop12_value]
    change (UInt256.shiftLeft (EVM.word addr.val) ⟨96⟩).toNat / 2^96 = _
    rw [shiftLeft96_toNat_of_lt_160 _ (addressWord_val_canonical addr)]
    exact Nat.mul_div_cancel _ (by decide)

theorem packedAddressMask (addr : AccountAddress) :
    UInt256.land (UInt256.shiftLeft (UInt256.ofNat addr.val) (UInt256.ofNat 96))
      (UInt256.lnot (UInt256.ofNat 79228162514264337593543950335)) =
      UInt256.shiftLeft (UInt256.ofNat addr.val) (UInt256.ofNat 96) := by
  exact addressWord_shiftLeft96_high_mask addr

end Benchmarks.Midnight
