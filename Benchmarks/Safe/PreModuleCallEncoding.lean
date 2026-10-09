import Benchmarks.Safe.PreModuleEncodingRead
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def preModuleCallBytes (target value : UInt256) (payload : ByteArray)
    (operation sender : UInt256) : ByteArray :=
  checkModuleTransactionSelector ++
    wordBytes [UInt256.land target solcAddrMask, value, UInt256.ofNat 160,
      operation, UInt256.land solcAddrMask sender, UInt256.ofNat payload.size] ++
    payload ++ ByteArray.zeroes (ABI.paddedSize payload.size - payload.size)

-- LIBRARY CANDIDATE: the small unsigned ABI integer uses the same canonical word encoding.
theorem encodeABIValue_uint_word (bits : BitWidth) (word : UInt256)
    (hbits : bits.val ≠ 0) (hword : word.toNat < EVM.twoPow bits.val) :
    encodeABIValue? (.elem (.int (.uint bits))) (.int (Int.ofNat word.toNat)) =
      some (EVM.Word.toBytesBE word) := by
  have he : EVM.word word.toNat = word := u256_ofNat_toNat word
  simp [encodeABIValue?, encodeABIWord?, hbits, hword, he]

set_option maxRecDepth 10000 in
theorem safePreModuleCallEncoding (target value : UInt256) (payload : ByteArray)
    (operation sender : UInt256) (ho : operation.toNat < 256) :
    config.externalABI.encode? "checkModuleTransaction"
      [.address (AccountAddress.ofUInt256 target), .int (Int.ofNat value.toNat),
        .bytes payload, .int (Int.ofNat operation.toNat),
        .address (AccountAddress.ofUInt256 sender)] =
      some (preModuleCallBytes target value payload operation sender) := by
  have ht := encodeABIValue_address_word target
  have hv := encodeABIValue_uint256_word value
  have hs := encodeABIValue_address_word sender
  have hop := encodeABIValue_uint_word ⟨8, by decide⟩ operation (by decide) ho
  change ABI.encodeCallWithSelector? checkModuleTransactionSelector
    [addr, uint256, bytesTy, uint8, addr] _ = _
  rw [← addressOfNat_eq_of_masked_word] at ht hs
  simp only [addr, uint256, uint256Int, bytesTy, uint8, uint8Int,
    accountAddress_ofUInt256_eq_ofNat_toNat, abiAddress, abiUInt256, abiUInt256Int] at ht hv hs ⊢
  simp only [encodeCallWithSelector?, encodeABIValues?,
    abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, encodeABIValuesFrom?,
    ht, hv, hs, hop, bind, Option.bind, pure, Bool.false_eq_true, Bool.true_eq,
    ite_false, ite_true, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero]
  simp only [encodeABIValue?, bind, Option.bind, pure, List.nil_append, List.append_nil,
    list_toByteArray_append, natBytes_toByteArray, padRightToWord_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray, byteArray_toList_toByteArray]
  simp only [preModuleCallBytes, wordBytes, u256_land_comm, ByteArray.append_empty,
    ByteArray.append_assoc]

end Benchmarks.Safe
