import Solm.Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: reject a truncated static tuple independently of its scalar value types.
theorem decodeCalldata_scalar_none_short {cd : ByteArray} {names : List Ident}
    {types : List ABIType} (hscalar : types.all isABIScalarWordType = true)
    (hshort : cd.size < 4 + 32 * types.length) : decodeCalldata names types cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq hscalar]
  split_ifs
  · rfl
  · rfl
  · cases hd : decodeScalarWords? types (cd.toList.drop 4) 0 with
    | none => rfl
    | some values =>
        have hlen := decodeScalarWords?_some_length (Nat.zero_le _) hd
        rw [List.length_drop, htlen] at hlen
        omega

-- LIBRARY CANDIDATE: solc's signed huge-calldata guard for any nonempty static tuple.
theorem decodeCalldata_scalar_none_huge {cd : ByteArray} {names : List Ident}
    {types : List ABIType} (hscalar : types.all isABIScalarWordType = true)
    (hnil : types.isEmpty = false) (hhuge : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata names types cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq hscalar]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos ⟨hnil, by rw [List.length_drop, htlen]; omega⟩]

end Auction
