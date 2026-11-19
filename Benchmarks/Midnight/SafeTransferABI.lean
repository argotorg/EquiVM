import Benchmarks.Midnight.WordTuple
import Reasoning.ABIComposite

/-! Static calldata and return decoding for the two token-transfer helpers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def safeTransferCallArgs (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    List Value :=
  (if isFrom then [.address sender] else []) ++
    [.address recipient, .int (Int.ofNat value.toNat)]

def safeTransferCallWords (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    List UInt256 :=
  (if isFrom then [UInt256.ofNat sender.val] else []) ++
    [UInt256.ofNat recipient.val, value]

def safeTransferSelector (isFrom : Bool) : ByteArray :=
  if isFrom then ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ else ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩

def safeTransferSelectorWord (isFrom : Bool) : UInt256 :=
  UInt256.ofNat ((if isFrom then 0x23b872dd else 0xa9059cbb) * 2 ^ 224)

def safeTransferCalldata (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    ByteArray :=
  safeTransferSelector isFrom ++ wordArrayBytes (safeTransferCallWords isFrom sender recipient value)

theorem safeTransferSelectorWord_bytes (isFrom : Bool) :
    (safeTransferSelectorWord isFrom).toByteArray.extract 0 4 = safeTransferSelector isFrom := by
  cases isFrom <;> decide +kernel

theorem safeTransferCalldata_size (isFrom : Bool) (sender recipient : AccountAddress)
    (value : UInt256) :
    (safeTransferCalldata isFrom sender recipient value).size = if isFrom then 100 else 68 := by
  cases isFrom <;>
    simp [safeTransferCalldata, safeTransferSelector, safeTransferCallWords, wordArrayBytes] <;> rfl

theorem encodeABIValue_accountAddress (a : AccountAddress) :
    encodeABIValue? abiAddress (.address a) = some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
  simp [abiAddress, encodeABIValue?, encodeABIWord?]
  rfl

theorem encodeSafeTransfer (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    config.externalABI.encode? (if isFrom then "transferFrom" else "transfer")
      (safeTransferCallArgs isFrom sender recipient value) =
      some (safeTransferCalldata isFrom sender recipient value) := by
  have hs := encodeABIValue_accountAddress sender
  have hr := encodeABIValue_accountAddress recipient
  have hv := encodeABIValue_uint256 value
  cases isFrom <;>
    simp only [config, externalABI, safeTransferCallArgs, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append, Model.abiValues, Model.abiValue, String.reduceEq,
      encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, staticABIEncodedSize?,
      isDynamicABIType, bind, Option.bind, encodeABIValuesFrom?, hs, hr, hv,
      List.nil_append, List.append_nil, safeTransferCalldata, safeTransferSelector,
      safeTransferCallWords, wordArrayBytes, ByteArray.append_empty]
  all_goals
    simp only [List.toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
      ByteArray.append_assoc]

end Benchmarks.Midnight
