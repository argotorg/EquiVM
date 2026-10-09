import Benchmarks.Morpho.MorphoBlue.CalldataBytesABI
import Benchmarks.Morpho.MorphoBlue.MarketParamsABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the address/uint256/bytes ABI head with modern-solc bounds.
def AddressWordBytesBounds (cd : ByteArray) : Prop :=
  100 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧
    (calldataWord cd 4).toNat < EVM.addressModulus ∧
    (calldataWord cd 68).toNat ≤ solcMaxU64 ∧
    CalldataBytesBounds cd (4 + (calldataWord cd 68).toNat)

instance (cd : ByteArray) : Decidable (AddressWordBytesBounds cd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def addressWordBytesArgs (cd : ByteArray) (a b c : Ident) : Store :=
  (((∅ : Store).insert a (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert
    b (.int (Int.ofNat (calldataWord cd 36).toNat))).insert
    c (.bytes (calldataBytesPayload cd (4 + (calldataWord cd 68).toNat)))

theorem decodeCalldata_address_uint256_bytes_eq (cd : ByteArray) (a b c : Ident) :
    decodeCalldata [a, b, c] [abiAddress, abiUInt256, .bytes] cd =
      if AddressWordBytesBounds cd then some (addressWordBytesArgs cd a b c) else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : abiTupleHeadSize? [abiAddress, abiUInt256, .bytes] = some 96 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiAddress, abiUInt256]
  unfold decodeCalldata
  simp only [htlen, List.length_drop,
    show [abiAddress, abiUInt256, ABIType.bytes].any isDynamicABIType = true from rfl,
    true_and, List.isEmpty_cons, solcTotalSizeDynamicGuard, Bool.false_eq_true, false_and]
  by_cases h4 : cd.size < 4
  · simp only [h4, ↓reduceIte, show ¬ AddressWordBytesBounds cd from fun h => by have := h.1; omega]
  · simp only [h4, ↓reduceIte]
    by_cases hh : cd.size < 2 ^ 255
    swap
    · simp only [show 2 ^ 255 ≤ cd.size by omega, ↓reduceIte,
        show ¬ AddressWordBytesBounds cd from fun h => hh h.2.1]
    simp only [show ¬ 2 ^ 255 ≤ cd.size by omega, show ¬ 2 ^ 255 ≤ cd.size - 4 by omega,
      ↓reduceIte, decodeCalldata.decodeArgs, hhead, bind, Option.bind, List.length_drop, htlen]
    by_cases hs : 100 ≤ cd.size
    swap
    · simp only [show cd.size - 4 < 96 by omega, ↓reduceIte,
        show ¬ AddressWordBytesBounds cd from fun h => hs h.1]
    simp only [show ¬ cd.size - 4 < 96 by omega, ↓reduceIte,
      decodeABIValues?, show isDynamicABIType abiAddress = false from rfl,
      show staticABIEncodedSize? abiAddress = some 32 from rfl,
      Bool.false_eq_true, ↓reduceIte, bind, Option.bind, Nat.zero_add]
    rw [decodeABIValue_scalarWord_eq (by decide)]
    by_cases ha : (calldataWord cd 4).toNat < EVM.addressModulus
    swap
    · have hn := decodeScalarWord_calldata_address_noncanonical (cd := cd) (off := 0) (by omega) (by decide) ha
      simp only [hn, Option.bind_none, show ¬ AddressWordBytesBounds cd from fun h => ha h.2.2.1,
        ↓reduceIte]
    have had := decodeScalarWord_calldata_address (cd := cd) (off := 0) (by omega) (by decide) ha
    simp only [had, Option.bind_some, ↓reduceIte, Nat.reduceAdd,
      show isDynamicABIType abiUInt256 = false from rfl,
      show staticABIEncodedSize? abiUInt256 = some 32 from rfl, Bool.false_eq_true]
    rw [decodeABIValue_scalarWord_eq (by decide)]
    have hwd := decodeScalarWord_calldata_uint256 (cd := cd) (off := 32) (by omega) (by decide)
    rw [hwd]
    simp only [↓reduceIte, Nat.reduceAdd,
      show isDynamicABIType ABIType.bytes = true from rfl]
    have hro := readNat_drop4_at_eq_calldataWord (cd := cd) 64 (by omega)
    rw [hro]
    simp only [solcMaxLen]
    by_cases ho : (calldataWord cd 68).toNat ≤ solcMaxU64
    swap
    · simp only [show solcMaxU64 < (calldataWord cd 68).toNat by omega, ↓reduceIte,
        show ¬ AddressWordBytesBounds cd from fun h => ho h.2.2.2.1]
    simp only [show ¬ solcMaxU64 < (calldataWord cd 68).toNat by omega, ↓reduceIte, Nat.zero_add]
    rw [decodeABIValue_bytes_calldata_eq]
    by_cases hb : CalldataBytesBounds cd (4 + (calldataWord cd 68).toNat)
    · simp only [hb, ↓reduceIte, Option.bind_some, decodeCalldata.insertValues,
        show AddressWordBytesBounds cd from ⟨hs, hh, ha, ho, hb⟩, addressWordBytesArgs]
    · simp only [hb, ↓reduceIte, Option.bind_none,
        show ¬ AddressWordBytesBounds cd from fun h => hb h.2.2.2.2]

end Benchmarks.Morpho.MorphoBlue
