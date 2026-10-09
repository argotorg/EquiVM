import Benchmarks.CompoundIII.Comet.ZeroCallBridge
import Benchmarks.CompoundIII.Comet.CallWordsMemory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferSelectorWord : UInt256 := UInt256.shiftLeft ⟨2835717307⟩ ⟨224⟩

def transferPayload (recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  (ByteArray.mk #[169, 5, 156, 187] ++ (EVM.word recipient.val).toByteArray) ++ amount.toByteArray

theorem transferPayload_size (recipient : AccountAddress) (amount : UInt256) :
    (transferPayload recipient amount).size = 68 := by
  simp only [transferPayload, ByteArray.size_append, toByteArray_size]
  rfl

theorem transferPayload_encode (recipient : AccountAddress) (amount : UInt256) :
    config.externalABI.encode? "transfer" [.address recipient, .int (Int.ofNat amount.toNat)] =
      some (transferPayload recipient amount) := by
  change encodeCallWithSelector? (selectorBytes 169 5 156 187)
    [abiAddress, abiUInt256] [.address recipient, .int (Int.ofNat amount.toNat)] = _
  unfold encodeCallWithSelector?
  rw [encodeABIValues?, abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?,
    (encodeABIValue_this_address { (default : ExecutionEnv) with codeOwner := recipient })]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?, encodeABIValue_uint256_word]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?]
  simp only [bind, Option.bind, List.append_nil, List.nil_append]
  congr 1
  apply ByteArray.ext
  simp [transferPayload, selectorBytes, byteArray_toList_eq, List.append_toArray,
    List.append_assoc, Array.append_assoc]

def transferInputMemory (mem : ByteArray) (ptr : UInt256) (recipient : AccountAddress)
    (amount : UInt256) : ByteArray :=
  callTwoWordMemory mem ptr transferSelectorWord (EVM.word recipient.val) amount

theorem transferInputMemory_payload {mem : ByteArray} {ptr amount : UInt256}
    {recipient : AccountAddress} (hb : ptr.toNat + 68 < 2^64) :
    (transferInputMemory mem ptr recipient amount).readWithPadding ptr.toNat 68 =
      transferPayload recipient amount := by
  have hsel : transferSelectorWord.toByteArray.extract 0 4 =
      ByteArray.mk #[169, 5, 156, 187] := by decide +kernel
  exact (callTwoWordMemory_payload hb).trans (by rw [hsel]; rfl)

end Benchmarks.CompoundIII.Comet
