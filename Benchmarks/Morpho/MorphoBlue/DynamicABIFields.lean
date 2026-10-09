import Benchmarks.Morpho.MorphoBlue.DynamicABIHead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: peel a statically encoded head value before an arbitrary ABI tail.
theorem decodeABIValues_static_cons {ty : ABIType} {types : List ABIType}
    {bytes : List UInt8} {base cursor head last size : Nat}
    (hd : isDynamicABIType ty = false) (hs : staticABIEncodedSize? ty = some size) :
    decodeABIValues? (ty :: types) bytes base cursor head last =
      (decodeABIValue? ty bytes (base + cursor)).bind (fun pair ↦
        if pair.2 = base + cursor + size then
          (decodeABIValues? types bytes base (cursor + size) head (max last pair.2)).map
            (fun rest ↦ (pair.1 :: rest.1, rest.2))
        else none) := by
  rw [decodeABIValues?]
  simp only [hd, Bool.false_eq_true, ↓reduceIte, hs, bind, Option.bind_some]
  cases decodeABIValue? ty bytes (base + cursor) with
  | none => rfl
  | some pair =>
    simp only [Option.bind_some]
    by_cases hp : pair.2 = base + cursor + size
    · simp only [if_pos hp]
      cases decodeABIValues? types bytes base (cursor + size) head (max last pair.2) <;> rfl
    · simp only [if_neg hp]

-- LIBRARY CANDIDATE: uint256 head decoding at an arbitrary calldata word offset.
theorem decodeABIValues_calldata_uint_cons {cd : ByteArray} {types : List ABIType}
    {cursor head last : Nat} (hb : 4 + cursor + 32 ≤ cd.size) (hh : cursor + 36 < 2 ^ 64) :
    decodeABIValues? (abiUInt256 :: types) (cd.toList.drop 4) 0 cursor head last =
      (decodeABIValues? types (cd.toList.drop 4) 0 (cursor + 32) head
        (max last (cursor + 32))).map
        (fun rest ↦ (.int (Int.ofNat (calldataWord cd (4 + cursor)).toNat) :: rest.1, rest.2)) := by
  rw [decodeABIValues_static_cons rfl rfl,
    decodeABIValue_scalarWord_eq (by decide),
    decodeScalarWord_calldata_uint256 (by omega) (by omega)]
  simp only [Nat.zero_add, Option.bind_some, ↓reduceIte, Nat.add_comm]

-- LIBRARY CANDIDATE: canonical-address and dynamic-bytes guards for an ABI tail.
def AddressBytesBounds (cd : ByteArray) (cursor : Nat) : Prop :=
  (calldataWord cd (4 + cursor)).toNat < EVM.addressModulus ∧
    (calldataWord cd (4 + (cursor + 32))).toNat ≤ solcMaxU64 ∧
    CalldataBytesBounds cd (4 + (calldataWord cd (4 + (cursor + 32))).toNat)

instance (cd : ByteArray) (cursor : Nat) : Decidable (AddressBytesBounds cd cursor) := by
  unfold AddressBytesBounds
  infer_instance

theorem decodeABIValues_calldata_address_bytes {cd : ByteArray} {cursor head last : Nat}
    (hb : 4 + cursor + 64 ≤ cd.size) (hh : cursor + 36 < 2 ^ 64) :
    (decodeABIValues? [abiAddress, .bytes] (cd.toList.drop 4) 0 cursor head last).map Prod.fst =
      if AddressBytesBounds cd cursor then
        some [.address (AccountAddress.ofNat (calldataWord cd (4 + cursor)).toNat),
          .bytes (calldataBytesPayload cd (4 + (calldataWord cd (4 + (cursor + 32))).toNat))]
      else none := by
  rw [decodeABIValues_static_cons rfl rfl, decodeABIValue_scalarWord_eq (by decide)]
  by_cases ha : (calldataWord cd (4 + cursor)).toNat < EVM.addressModulus
  swap
  · rw [decodeScalarWord_calldata_address_noncanonical (by omega) (by omega) (by simpa only [Nat.add_comm] using ha)]
    simp only [Option.bind_none, Option.map_none,
      show ¬ AddressBytesBounds cd cursor from fun h ↦ ha h.1, ↓reduceIte]
  rw [decodeScalarWord_calldata_address (by omega) (by omega) (by simpa only [Nat.add_comm] using ha)]
  simp only [Nat.zero_add, Option.bind_some, ↓reduceIte, decodeABIValues?,
    show isDynamicABIType ABIType.bytes = true from rfl, bind, Option.bind]
  rw [readNat_drop4_at_eq_calldataWord (cursor + 32) (by omega)]
  simp only [solcMaxLen]
  by_cases ho : (calldataWord cd (4 + (cursor + 32))).toNat ≤ solcMaxU64
  swap
  · simp only [show solcMaxU64 < (calldataWord cd (4 + (cursor + 32))).toNat by omega,
      ↓reduceIte, Option.map_none,
      show ¬ AddressBytesBounds cd cursor from fun h ↦ ho h.2.1]
  simp only [show ¬ solcMaxU64 < (calldataWord cd (4 + (cursor + 32))).toNat by omega,
    ↓reduceIte, Nat.zero_add]
  rw [decodeABIValue_bytes_calldata_eq]
  by_cases hp : CalldataBytesBounds cd (4 + (calldataWord cd (4 + (cursor + 32))).toNat)
  · simp only [hp, ↓reduceIte, Option.map_some,
      show AddressBytesBounds cd cursor from ⟨ha, ho, hp⟩, Nat.add_comm]
  · simp only [hp, ↓reduceIte, Option.map_none,
      show ¬ AddressBytesBounds cd cursor from fun h ↦ hp h.2.2]

end Benchmarks.Morpho.MorphoBlue
