import Benchmarks.Safe.Calldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a three-address static ABI tuple.
theorem decodeAddressTripleGuard {cd : ByteArray} {x y z : Solm.Ident}
    (hlong : 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [abiAddress, abiAddress, abiAddress] cd =
      if 2 ^ 255 ≤ cd.size - 4 then none
      else if cd.size - 4 < 96 then none
      else (do
        let (values, _) ← decodeABIValues? [abiAddress, abiAddress, abiAddress]
          (cd.toList.drop 4) 0 0 96 96
        decodeCalldata.insertValues [x, y, z] values ∅) :=
  decodeStaticCalldata hlong (by decide) (by decide)
    (by simp [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind])

theorem decodeAddressTripleValue {cd : ByteArray} {offset : Nat}
    (hlen : offset + 32 ≤ cd.size) (hoffset : 4 ≤ offset) :
    decodeABIValue? abiAddress (cd.toList.drop 4) (offset - 4) =
      if (calldataWord cd offset).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd offset).toNat), offset - 4 + 32)
      else none := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : (((cd.toList.drop 4).drop (offset - 4)).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hl]; omega
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop (offset - 4)).take 32) =
      calldataWord cd offset := by
    rw [List.drop_drop, Nat.add_sub_of_le hoffset]
    exact decode_word_at_eq_any cd offset hlen
  by_cases hc : (calldataWord cd offset).toNat < EVM.addressModulus
  · rw [if_pos hc, decodeABIValue_address_ok ht (by rw [hw]; exact hc), hw]
  · rw [if_neg hc, decodeABIValue_address_none_noncanon ht (by rw [hw]; exact hc)]

theorem decodeAddressTriple {cd : ByteArray} {x y z : Solm.Ident}
    (hlen : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y, z] [abiAddress, abiAddress, abiAddress] cd =
      if (calldataWord cd 4).toNat < EVM.addressModulus ∧
          (calldataWord cd 36).toNat < EVM.addressModulus ∧
          (calldataWord cd 68).toNat < EVM.addressModulus then
        some ((((∅ : Store).insert x
          (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
          (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
          (.address (AccountAddress.ofNat (calldataWord cd 68).toNat)))
      else none := by
  rw [decodeAddressTripleGuard (by omega), if_neg (by omega), if_neg (by omega)]
  have h₀ := decodeAddressTripleValue (offset := 4) (cd := cd) (by omega) (by omega)
  have h₁ := decodeAddressTripleValue (offset := 36) (cd := cd) (by omega) (by omega)
  have h₂ := decodeAddressTripleValue (offset := 68) (cd := cd) (by omega) (by omega)
  simp only [decodeABIValues?, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases hc0 : (calldataWord cd 4).toNat < EVM.addressModulus <;>
    by_cases hc1 : (calldataWord cd 36).toNat < EVM.addressModulus <;>
      by_cases hc2 : (calldataWord cd 68).toNat < EVM.addressModulus <;>
        simp [h₀, h₁, h₂, hc0, hc1, hc2, decodeCalldata.insertValues]

theorem decodeAddressTripleShort {cd : ByteArray} {x y z : Solm.Ident}
    (hlong : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [abiAddress, abiAddress, abiAddress] cd = none := by
  rw [decodeAddressTripleGuard hlong, if_neg (by omega), if_pos (by omega)]

theorem decodeAddressTripleHuge {cd : ByteArray} {x y z : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [abiAddress, abiAddress, abiAddress] cd = none := by
  rw [decodeAddressTripleGuard (by omega), if_pos (by omega)]

end Benchmarks.Safe
