import Benchmarks.CompoundIII.Comet.ZeroCallBridge
import Benchmarks.CompoundIII.Comet.CallWordsMemory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def approveSelectorWord : UInt256 := UInt256.shiftLeft ⟨157198259⟩ ⟨224⟩

def approvePayload (manager : AccountAddress) (amount : UInt256) : ByteArray :=
  (ByteArray.mk #[9, 94, 167, 179] ++ (EVM.word manager.val).toByteArray) ++ amount.toByteArray

theorem approvePayload_size (manager : AccountAddress) (amount : UInt256) :
    (approvePayload manager amount).size = 68 := by
  simp only [approvePayload, ByteArray.size_append, toByteArray_size]
  rfl

theorem approvePayload_encode (manager : AccountAddress) (amount : UInt256) :
    config.externalABI.encode? "approve" [.address manager, .int (Int.ofNat amount.toNat)] =
      some (approvePayload manager amount) := by
  change encodeCallWithSelector? (selectorBytes 9 94 167 179)
    [abiAddress, abiUInt256] [.address manager, .int (Int.ofNat amount.toNat)] = _
  unfold encodeCallWithSelector?
  rw [encodeABIValues?, abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?,
    (encodeABIValue_this_address { (default : ExecutionEnv) with codeOwner := manager })]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?, encodeABIValue_uint256_word]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?]
  simp only [List.append_nil, List.nil_append]
  congr 1
  apply ByteArray.ext
  simp [approvePayload, selectorBytes, byteArray_toList_eq, Array.append_assoc]

def approveInputMemory (mem : ByteArray) (ptr : UInt256) (manager : AccountAddress)
    (amount : UInt256) : ByteArray :=
  callTwoWordMemory mem ptr approveSelectorWord (EVM.word manager.val) amount

theorem approveInputMemory_payload {mem : ByteArray} {ptr amount : UInt256}
    {manager : AccountAddress} (hb : ptr.toNat + 68 < 2^64) :
    (approveInputMemory mem ptr manager amount).readWithPadding ptr.toNat 68 =
      approvePayload manager amount := by
  have hsel : approveSelectorWord.toByteArray.extract 0 4 =
      ByteArray.mk #[9, 94, 167, 179] := by decide +kernel
  exact (callTwoWordMemory_payload hb).trans (by rw [hsel]; rfl)

end Benchmarks.CompoundIII.Comet
