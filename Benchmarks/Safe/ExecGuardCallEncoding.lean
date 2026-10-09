import Benchmarks.Safe.ExecGuardEncodingRead
import Benchmarks.Safe.ExecTransactionInput
import Benchmarks.Safe.PreModuleCallEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def execGuardArguments (p : ExecTransactionInput) (sender : EVM.Address) : List Value :=
  [.address p.tx.target, uint256Value p.tx.value, .bytes p.tx.payload,
    uint256Value p.tx.operation, uint256Value p.tx.safeTxGas, uint256Value p.tx.baseGas,
    uint256Value p.tx.gasPrice, .address p.tx.gasToken, .address p.tx.refundReceiver,
    .bytes p.signatures, .address sender]

theorem safeExecGuardCallEncoding (p : ExecTransactionInput) (sender : EVM.Address)
    (ho : p.tx.operation.toNat < 256) :
    config.externalABI.encode? "checkTransaction" (execGuardArguments p sender) =
      some (checkTransactionSelector ++
        execGuardArgsBytes p.tx p.signatures (UInt256.ofNat sender.val)) := by
  have ha (a : EVM.Address) :
      encodeABIValue? addr (.address a) =
        some (UInt256.land (UInt256.ofNat a.val) solcAddrMask).toByteArray.toList := by
    have he := encodeABIValue_address_word (UInt256.ofNat a.val)
    rw [← addressOfNat_eq_of_masked_word,
      ← accountAddress_ofUInt256_eq_ofNat_toNat, accountAddress_roundtrip] at he
    exact he
  have hv := encodeABIValue_uint256_word p.tx.value
  have hsafe := encodeABIValue_uint256_word p.tx.safeTxGas
  have hbase := encodeABIValue_uint256_word p.tx.baseGas
  have hprice := encodeABIValue_uint256_word p.tx.gasPrice
  have hop := encodeABIValue_uint_word ⟨8, by decide⟩ p.tx.operation (by decide) ho
  have hlen : (natBytes p.tx.payload.size ++ padRightToWord p.tx.payload.toList).length =
      32 + ABI.paddedSize p.tx.payload.size := by
    simp only [List.length_append, natBytes, word_toBytesBE_length_32, padRightToWord,
      zeroBytes, List.length_replicate, byteArray_toList_eq, Array.length_toList]
    change 32 + (p.tx.payload.size + (ABI.paddedSize p.tx.payload.size - p.tx.payload.size)) = _
    unfold ABI.paddedSize
    omega
  change ABI.encodeCallWithSelector? checkTransactionSelector
    [addr, uint256, bytesTy, uint8, uint256, uint256, uint256, addr, addr, bytesTy, addr] _ = _
  simp only [execGuardArguments, uint256Value]
  simp only [addr, uint256, uint256Int, bytesTy, uint8, uint8Int,
    abiAddress, abiUInt256, abiUInt256Int] at ha hv hsafe hbase hprice ⊢
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, ha, hv, hsafe, hbase, hprice, hop,
    bind, Option.bind, pure, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
    List.nil_append, List.append_nil, List.length_nil, Nat.add_zero]
  simp only [encodeABIValue?, bind, Option.bind, pure, List.nil_append, List.append_nil,
    list_toByteArray_append, natBytes_toByteArray, padRightToWord_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray, byteArray_toList_toByteArray]
  simp only [execGuardArgsBytes, execGuardStaticWords, execGuardHeadWords, execGuardMiddleWords,
    List.cons_append, List.nil_append, wordBytes, u256_land_comm, ByteArray.append_empty,
    ByteArray.append_assoc, hlen, Nat.reduceAdd,
    show 352 + (32 + ABI.paddedSize p.tx.payload.size) =
      384 + ABI.paddedSize p.tx.payload.size by omega]
  rfl

end Benchmarks.Safe
