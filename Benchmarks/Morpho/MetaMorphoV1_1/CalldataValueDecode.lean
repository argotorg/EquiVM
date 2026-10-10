import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Reasoning.ABI

/-! Decode static calldata fields at arbitrary offsets beyond the selector. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: share the selector-relative slice facts across static ABI fields.
theorem calldataFieldSlice {cd : ByteArray} {off : Nat} (hlen : 4 + off + 32 ≤ cd.size) :
    (((cd.toList.drop 4).drop off).take 32).length = 32 ∧
      bytesToWord (((cd.toList.drop 4).drop off).take 32) = calldataWord cd (4 + off) := by
  constructor
  · simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (cd.size - 4 - off) = 32
    omega
  · simpa only [List.drop_drop, Nat.add_comm] using decode_word_at_eq_any cd (4 + off) hlen

theorem decodeCalldataAddressField {cd : ByteArray} {off : Nat}
    (hlen : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? abiAddress (cd.toList.drop 4) off =
      if (calldataWord cd (4 + off)).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd (4 + off)).toNat), off + 32)
      else none := by
  obtain ⟨hl, hw⟩ := calldataFieldSlice hlen
  simp only [abiAddress, decodeABIValue?, readWord?, readBytes?, hl, if_true,
    bind, Option.bind, hw, decodeABIWord?]
  simp only [UInt256.toNat]
  split_ifs <;> rfl

theorem decodeCalldataUintField {cd : ByteArray} {off : Nat} (bits : BitWidth)
    (hlen : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? (.elem (.int (.uint bits))) (cd.toList.drop 4) off =
      if (calldataWord cd (4 + off)).toNat < EVM.twoPow bits.val then
        some (uint256Value (calldataWord cd (4 + off)), off + 32)
      else none := by
  obtain ⟨hl, hw⟩ := calldataFieldSlice hlen
  rw [decodeABIValue_scalarWord_eq (by rfl), decodeScalarWord_uint_result bits hl, hw]

theorem decodeCalldataWordField {cd : ByteArray} {off : Nat}
    (hlen : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? abiUInt256 (cd.toList.drop 4) off =
      some (uint256Value (calldataWord cd (4 + off)), off + 32) := by
  obtain ⟨hl, hw⟩ := calldataFieldSlice hlen
  simpa only [hw] using decodeABIValue_uint256_ok hl

theorem decodeCalldataBytes32Field {cd : ByteArray} {off : Nat}
    (hlen : 4 + off + 32 ≤ cd.size) :
    decodeABIValue? abiBytes32 (cd.toList.drop 4) off =
      some (wordBytes32Value (calldataWord cd (4 + off)), off + 32) := by
  obtain ⟨hl, hw⟩ := calldataFieldSlice hlen
  rw [decodeABIValue_bytes32_ok hl]
  simp only [wordBytes32Value, ← hw, toBytesBE_bytesToWord_of_length hl]

end Benchmarks.Morpho.MetaMorphoV1_1
