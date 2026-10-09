import Solidity.Semantics.Dispatch
import Reasoning.ABI

/-!
# Positional calldata decoding

`decodeCalldataValues?` is `ABI.decodeCalldata` with the argument positions as names, read back in
order; the shapes below (the calldata decodings the examples need) follow from the store-shaped
facts of `Reasoning/ABI.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Solidity

open Ethereum Reasoning.Theory

theorem argNames_zero : argNames 0 = [] := rfl
theorem argNames_one : argNames 1 = ["#0"] := by decide
theorem argNames_two : argNames 2 = ["#0", "#1"] := by decide
theorem argNames_three : argNames 3 = ["#0", "#1", "#2"] := by decide

/-- Read the positional names back out of the store the decoder bound them in. -/
macro "decode_read" : tactic =>
  `(tactic| simp +decide [Option.bind, List.mapM, List.mapM.loop, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty, -getElem?_pos, -getElem?_neg])

/-! ## No arguments -/

theorem decodeCalldataValues_empty_ok {cd : ByteArray} (hsz4 : 4 ≤ cd.size) :
    decodeCalldataValues? [] cd = some [] := by
  unfold decodeCalldataValues?
  rw [List.length_nil, argNames_zero, decodeCalldata_empty_ok hsz4]
  rfl

/-! ## `(address)` -/

theorem decodeCalldataValues_address_ok {cd : ByteArray}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address] cd =
      some [.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat)] := by
  unfold decodeCalldataValues?
  rw [List.length_singleton, argNames_one, decodeCalldata_address_ok hsz36 hbig hcanon]
  decode_read

theorem decodeCalldataValues_address_none_noncanon {cd : ByteArray}
    (hsz36 : 36 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [List.length_singleton, argNames_one, decodeCalldata_address_none_noncanon hsz36 hbig hnc]
  rfl

theorem decodeCalldataValues_address_none_short {cd : ByteArray} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataValues? [.elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [List.length_singleton, argNames_one, decodeCalldata_address_none_short hsz4 hshort]
  rfl

theorem decodeCalldataValues_address_none_huge {cd : ByteArray} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataValues? [.elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [List.length_singleton, argNames_one, decodeCalldata_address_none_huge hbig]
  rfl

/-! ## `(address, uint256)` -/

theorem decodeCalldataValues_addr_uint256_ok {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, abiUInt256] cd =
      some [.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat),
        .int (Int.ofNat (calldataWord cd 36).toNat)] := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, abiUInt256].length = 2 from rfl, argNames_two,
    decodeCalldata_addr_uint256_ok hsz68 hbig hcanon]
  decode_read

theorem decodeCalldataValues_addr_uint256_none_noncanon {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, abiUInt256].length = 2 from rfl, argNames_two,
    decodeCalldata_addr_uint256_none_noncanon hsz68 hbig hnc]
  rfl

theorem decodeCalldataValues_addr_uint256_none_short {cd : ByteArray} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataValues? [.elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, abiUInt256].length = 2 from rfl, argNames_two,
    decodeCalldata_addr_uint256_none_short hsz4 hshort]
  rfl

theorem decodeCalldataValues_addr_uint256_none_huge {cd : ByteArray} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataValues? [.elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, abiUInt256].length = 2 from rfl, argNames_two,
    decodeCalldata_addr_uint256_none_huge hbig]
  rfl

/-! ## `(address, address)` -/

theorem decodeCalldataValues_address_address_ok {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address] cd =
      some [.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat),
        .address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat)] := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address].length = 2 from rfl, argNames_two,
    decodeCalldata_address_address_ok hsz68 hbig hcanon0 hcanon1]
  decode_read

theorem decodeCalldataValues_address_address_none_noncanon0 {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address].length = 2 from rfl, argNames_two,
    decodeCalldata_address_address_none_noncanon0 hsz68 hbig hnc0]
  rfl

theorem decodeCalldataValues_address_address_none_noncanon1 {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address].length = 2 from rfl, argNames_two,
    decodeCalldata_address_address_none_noncanon1 hsz68 hbig hcanon0 hnc1]
  rfl

theorem decodeCalldataValues_address_address_none_short {cd : ByteArray} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 68) : decodeCalldataValues? [.elem .address, .elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address].length = 2 from rfl, argNames_two,
    decodeCalldata_address_address_none_short hsz4 hshort]
  rfl

theorem decodeCalldataValues_address_address_none_huge {cd : ByteArray} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataValues? [.elem .address, .elem .address] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address].length = 2 from rfl, argNames_two,
    decodeCalldata_address_address_none_huge hbig]
  rfl

/-! ## `(address, address, uint256)` -/

theorem decodeCalldataValues_address_address_uint256_ok {cd : ByteArray}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address, abiUInt256] cd =
      some [.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat),
        .address (Ethereum.AccountAddress.ofNat (calldataWord cd 36).toNat),
        .int (Int.ofNat (calldataWord cd 68).toNat)] := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address, abiUInt256].length = 3 from rfl, argNames_three,
    decodeCalldata_address_address_uint256_ok hsz100 hbig hcanon0 hcanon1]
  decode_read

theorem decodeCalldataValues_address_address_uint256_none_noncanon0 {cd : ByteArray}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc0 : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address, abiUInt256].length = 3 from rfl, argNames_three,
    decodeCalldata_address_address_uint256_none_noncanon0 hsz100 hbig hnc0]
  rfl

theorem decodeCalldataValues_address_address_uint256_none_noncanon1 {cd : ByteArray}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon0 : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hnc1 : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataValues? [.elem .address, .elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address, abiUInt256].length = 3 from rfl, argNames_three,
    decodeCalldata_address_address_uint256_none_noncanon1 hsz100 hbig hcanon0 hnc1]
  rfl

theorem decodeCalldataValues_address_address_uint256_none_short {cd : ByteArray} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 100) : decodeCalldataValues? [.elem .address, .elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address, abiUInt256].length = 3 from rfl, argNames_three,
    decodeCalldata_address_address_uint256_none_short hsz4 hshort]
  rfl

theorem decodeCalldataValues_address_address_uint256_none_huge {cd : ByteArray} (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldataValues? [.elem .address, .elem .address, abiUInt256] cd = none := by
  unfold decodeCalldataValues?
  rw [show [ABI.ABIType.elem .address, .elem .address, abiUInt256].length = 3 from rfl, argNames_three,
    decodeCalldata_address_address_uint256_none_huge hbig]
  rfl

end Solidity
