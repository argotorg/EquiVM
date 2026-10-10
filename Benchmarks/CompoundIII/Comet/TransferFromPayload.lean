import Benchmarks.CompoundIII.Comet.TransferPayload
import Benchmarks.CompoundIII.Comet.CallThreeWordMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferFromSelectorWord : UInt256 := UInt256.shiftLeft ⟨599290589⟩ ⟨224⟩

def transferFromPayload (sender recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  ((ByteArray.mk #[35, 184, 114, 221] ++ (EVM.word sender.val).toByteArray) ++
    (EVM.word recipient.val).toByteArray) ++ amount.toByteArray

theorem transferFromPayload_size (sender recipient : AccountAddress) (amount : UInt256) :
    (transferFromPayload sender recipient amount).size = 100 := by
  simp only [transferFromPayload, ByteArray.size_append, toByteArray_size]
  rfl

theorem transferFromPayload_encode (sender recipient : AccountAddress) (amount : UInt256) :
    config.externalABI.encode? "transferFrom"
      [.address sender, .address recipient, .int (Int.ofNat amount.toNat)] =
      some (transferFromPayload sender recipient amount) := by
  change encodeCallWithSelector? (selectorBytes 35 184 114 221)
    [abiAddress, abiAddress, abiUInt256]
    [.address sender, .address recipient, .int (Int.ofNat amount.toNat)] = _
  unfold encodeCallWithSelector?
  rw [encodeABIValues?, abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?,
    (encodeABIValue_this_address { (default : ExecutionEnv) with codeOwner := sender })]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?,
    (encodeABIValue_this_address { (default : ExecutionEnv) with codeOwner := recipient })]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?, encodeABIValue_uint256_word]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?]
  simp only [bind, Option.bind, List.append_nil, List.nil_append]
  congr 1
  apply ByteArray.ext
  simp [transferFromPayload, selectorBytes, byteArray_toList_eq, List.append_toArray,
    List.append_assoc, Array.append_assoc]

def transferFromInputMemory (mem : ByteArray) (ptr : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) : ByteArray :=
  callThreeWordMemory mem ptr transferFromSelectorWord (EVM.word sender.val) (EVM.word recipient.val) amount

theorem transferFromInputMemory_payload {mem : ByteArray} {ptr amount : UInt256}
    {sender recipient : AccountAddress} (hb : ptr.toNat + 100 < 2^64) :
    (transferFromInputMemory mem ptr sender recipient amount).readWithPadding ptr.toNat 100 =
      transferFromPayload sender recipient amount := by
  have hsel : transferFromSelectorWord.toByteArray.extract 0 4 =
      ByteArray.mk #[35, 184, 114, 221] := by decide +kernel
  exact (callThreeWordMemory_payload hb).trans (by rw [hsel]; rfl)

end Benchmarks.CompoundIII.Comet
