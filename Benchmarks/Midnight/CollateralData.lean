import Benchmarks.Midnight.SafeTransferABI

/-! Typed collateral tuples and their word representation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure CollateralData where
  token : AccountAddress
  lltv : UInt256
  liquidationCursor : UInt256
  oracle : AccountAddress

def CollateralData.value (c : CollateralData) : Value :=
  .tuple [.address c.token, .int (Int.ofNat c.lltv.toNat),
    .int (Int.ofNat c.liquidationCursor.toNat), .address c.oracle]

def CollateralData.words (c : CollateralData) : List UInt256 :=
  [UInt256.ofNat c.token.val, c.lltv, c.liquidationCursor, UInt256.ofNat c.oracle.val]

def CollateralData.at (bytes : ByteArray) (start : Nat) : CollateralData :=
  ⟨AccountAddress.ofNat (calldataWord bytes start).toNat,
    calldataWord bytes (start + 32), calldataWord bytes (start + 64),
    AccountAddress.ofNat (calldataWord bytes (start + 96)).toNat⟩

def CollateralData.canonicalAt (bytes : ByteArray) (start : Nat) : Prop :=
  (calldataWord bytes start).toNat < EVM.addressModulus ∧
  (calldataWord bytes (start + 96)).toNat < EVM.addressModulus

instance (bytes : ByteArray) (start : Nat) : Decidable (CollateralData.canonicalAt bytes start) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem CollateralData.abiValue (c : CollateralData) : Model.abiValue c.value = c.value := rfl

theorem CollateralData.at_words {bytes : ByteArray} {start : Nat}
    (h : CollateralData.canonicalAt bytes start) :
    (CollateralData.at bytes start).words =
      [calldataWord bytes start, calldataWord bytes (start + 32),
        calldataWord bytes (start + 64), calldataWord bytes (start + 96)] := by
  have ht : UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes start).toNat).val =
      calldataWord bytes start := addressWord_eq_ofNat_address h.1
  have ho : UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes (start + 96)).toNat).val =
      calldataWord bytes (start + 96) := addressWord_eq_ofNat_address h.2
  simp only [CollateralData.at, CollateralData.words, ht, ho]

theorem CollateralData.encode (c : CollateralData) :
    encodeABIValue? Model.collateralABI c.value = some (wordArrayBytes c.words).toList := by
  have ht := encodeABIValue_accountAddress c.token
  have hl := encodeABIValue_uint256 c.lltv
  have hc := encodeABIValue_uint256 c.liquidationCursor
  have ho := encodeABIValue_accountAddress c.oracle
  simp only [Model.collateralABI, CollateralData.value, encodeABIValue?, encodeABIValues?,
    abiTupleHeadSize?, Model.addr, Model.u256, isDynamicABIType, staticABIEncodedSize?,
    Bool.false_eq_true, if_false, bind, Option.bind, encodeABIValuesFrom?,
    ht, hl, hc, ho, List.nil_append, List.append_nil]
  simp only [CollateralData.words, wordArrayBytes, byteArray_toList_append,
    word_toBytesBE_eq_toByteArray_toList, List.append_assoc, ByteArray.append_empty]

theorem CollateralData.array_encode (values : List CollateralData) :
    encodeABIStaticArrayElems? Model.collateralABI (values.map CollateralData.value) =
      some (wordArrayBytes (values.flatMap CollateralData.words)).toList := by
  induction values with
  | nil => simp [encodeABIStaticArrayElems?, wordArrayBytes, byteArray_toList_eq]
  | cons value rest ih =>
    simp only [List.map_cons, encodeABIStaticArrayElems?, CollateralData.encode,
      bind, Option.bind, ih, List.flatMap_cons]
    rw [wordArrayBytes_append, byteArray_toList_append]

end Benchmarks.Midnight
