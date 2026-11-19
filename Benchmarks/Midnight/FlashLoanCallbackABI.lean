import Benchmarks.Midnight.SafeTransferABI
import Benchmarks.Midnight.CalldataArrayWords
import Benchmarks.Midnight.FlashLoanMagicMemory

/-! ABI arguments and bytes32 replies of the flash-loan callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem abiValues_wordArray (words : List UInt256) :
    Model.abiValues (wordArrayValues words) = wordArrayValues words := by
  induction words with
  | nil => rfl
  | cons w ws ih => simpa only [wordArrayValues, List.map_cons, Model.abiValues,
      Model.abiValue] using congrArg (List.cons (.int (Int.ofNat w.toNat))) ih

theorem abiValues_addressWordArray (words : List UInt256) :
    Model.abiValues (addressWordArrayValues words) = addressWordArrayValues words := by
  induction words with
  | nil => rfl
  | cons w ws ih => simpa only [addressWordArrayValues, List.map_cons, Model.abiValues,
      Model.abiValue] using congrArg (List.cons (.address (AccountAddress.ofNat w.toNat))) ih

theorem encodeAddressWordArrayElems (words : List UInt256) (hc : CanonicalAddressWords words) :
    encodeABIStaticArrayElems? abiAddress (addressWordArrayValues words) =
      some (wordArrayBytes words).toList := by
  induction words with
  | nil => simp [addressWordArrayValues, wordArrayBytes, encodeABIStaticArrayElems?,
      byteArray_toList_eq]
  | cons w ws ih =>
    have hw := word_of_addressOfUInt256_of_canonical w (hc w List.mem_cons_self)
    rw [accountAddress_ofUInt256_eq_ofNat_toNat] at hw
    change UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w at hw
    simp only [addressWordArrayValues] at ih ⊢
    simp only [List.map_cons, encodeABIStaticArrayElems?,
      encodeABIValue_accountAddress, hw, bind, Option.bind]
    rw [ih (fun w h ↦ hc w (List.mem_cons_of_mem _ h))]
    simp only [wordArrayBytes, byteArray_toList_append, word_toBytesBE_eq_toByteArray_toList]

def flashLoanCallbackArguments (sender : AccountAddress) (tokens assets : List UInt256)
    (data : ByteArray) : List Value :=
  [.address sender, .array (addressWordArrayValues tokens), .array (wordArrayValues assets),
    .bytes data]

def flashLoanCallbackCalldata (sender : AccountAddress) (tokens assets : List UInt256)
    (data : ByteArray) : ByteArray :=
  ⟨#[0xd1, 0xf2, 0x60, 0xc3]⟩ ++
    wordArrayBytes [UInt256.ofNat sender.val, UInt256.ofNat 128,
      UInt256.ofNat (160 + 32 * tokens.length),
      UInt256.ofNat (192 + 32 * tokens.length + 32 * assets.length)] ++
    wordArrayBytes (UInt256.ofNat tokens.length :: tokens) ++
    wordArrayBytes (UInt256.ofNat assets.length :: assets) ++
    (UInt256.ofNat data.size).toByteArray ++ data ++
    ByteArray.zeroes (paddedSize data.size - data.size)

theorem encodeFlashLoanCallback (sender : AccountAddress) (tokens assets : List UInt256)
    (data : ByteArray) (hc : CanonicalAddressWords tokens) :
    config.externalABI.encode? "onFlashLoan" (flashLoanCallbackArguments sender tokens assets data) =
      some (flashLoanCallbackCalldata sender tokens assets data) := by
  have ht := encodeAddressWordArrayElems tokens hc
  have ha := encodeUIntWordArrayElems ⟨256, by decide⟩ assets (fun w _ ↦ w.val.isLt)
  have hs := encodeABIValue_accountAddress sender
  have het : encodeABIValue? (.dynamicArray abiAddress) (.array (addressWordArrayValues tokens)) =
      some (natBytes tokens.length ++ (wordArrayBytes tokens).toList) := by
    rw [encodeABIValue?]
    simp only [encodeABIArrayElems?, show isDynamicABIType abiAddress = false from rfl,
      Bool.false_eq_true, if_false, ht, bind, Option.bind]
    simp only [addressWordArrayValues, List.length_map]
  have hea : encodeABIValue? (.dynamicArray abiUInt256) (.array (wordArrayValues assets)) =
      some (natBytes assets.length ++ (wordArrayBytes assets).toList) := by
    rw [encodeABIValue?]
    simp only [encodeABIArrayElems?, show isDynamicABIType abiUInt256 = false from rfl,
      Bool.false_eq_true, if_false, ha, bind, Option.bind]
    simp only [wordArrayValues, List.length_map]
  have hb : encodeABIValue? .bytes (.bytes data) =
      some (natBytes data.size ++ padRightToWord data.toList) := by
    simp only [encodeABIValue?]
  have hl (b : ByteArray) : b.toList.length = b.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [config, externalABI, flashLoanCallbackArguments, Model.abiValues, Model.abiValue,
    abiValues_wordArray, abiValues_addressWordArray, String.reduceEq, if_true, if_false,
    encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, Bool.false_eq_true, bind, Option.bind,
    encodeABIValuesFrom?, hs, het, hea, hb,
    List.nil_append, List.append_nil]
  simp only [natBytes, word_toBytesBE_eq_toByteArray_toList, List.length_append,
    hl, toByteArray_size, wordArrayBytes_size]
  simp only [padRightToWord, hl, List.toByteArray_append,
    byteArray_toList_toByteArray, flashLoanCallbackCalldata, wordArrayBytes,
    ByteArray.append_empty, ByteArray.append_assoc]
  have hz (n : Nat) : (zeroBytes n).toByteArray = ByteArray.zeroes n := by
    have he : (ByteArray.zeroes n).toList = zeroBytes n := by
      simp [byteArray_toList_eq, ByteArray.zeroes, zeroBytes]
    rw [← he, byteArray_toList_toByteArray]
  simp only [hz, List.length_nil, Nat.add_zero, Nat.reduceAdd]
  have htlen : 128 + (32 + 32 * tokens.length) = 160 + 32 * tokens.length := by omega
  have halen : 128 + (32 + 32 * tokens.length + (32 + 32 * assets.length)) =
      192 + 32 * tokens.length + 32 * assets.length := by omega
  rw [htlen, halen]
  rfl

theorem decodeFlashLoanCallback {out : ByteArray} (h32 : 32 ≤ out.size) :
    config.externalABI.decode? "onFlashLoan" out =
      some [wordBytes32Value (calldataWord out 0)] := by
  change decodeReturnValues? [abiBytes32] (out.extract 0 32) = _
  have hs : (out.extract 0 32).toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (out.extract 0 32).size = 32
    rw [ByteArray.size_extract]; omega
  have hb : (out.extract 0 32).toList.take 32 = EVM.Word.toBytesBE (calldataWord out 0) := by
    rw [List.take_of_length_le (by omega), ← calldataWord_bytes h32,
      word_toBytesBE_eq_toByteArray_toList]
  rw [decodeReturnValues?, if_neg (by simp only [hs]; omega)]
  simp only [show abiTupleHeadSize? [abiBytes32] = some 32 from by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiBytes32, abiBytes32Width], bind, Option.bind]
  rw [decodeABIValues_bytes32_ok (by rw [List.length_take, hs]; rfl)]
  simp only [hb, wordBytes32Value]

theorem decodeFlashLoanCallback_short {out : ByteArray} (h32 : out.size < 32) :
    config.externalABI.decode? "onFlashLoan" out = none := by
  change decodeReturnValues? [abiBytes32] (out.extract 0 32) = _
  have hs : (out.extract 0 32).toList.length < 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (out.extract 0 32).size < 32
    rw [ByteArray.size_extract]; omega
  rw [decodeReturnValues?, if_neg (by omega)]
  simp only [show abiTupleHeadSize? [abiBytes32] = some 32 from by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiBytes32, abiBytes32Width], bind, Option.bind]
  rw [decodeABIValues_bytes32_none_short hs]

end Benchmarks.Midnight
