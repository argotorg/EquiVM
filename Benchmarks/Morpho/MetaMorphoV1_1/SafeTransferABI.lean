import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI

/-! The canonical transfer request shared by the source and bytecode call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def safeTransferSelector : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩

def safeTransferSelectorWord : UInt256 := UInt256.shiftLeft ⟨2835717307⟩ ⟨224⟩

def safeTransferCalldata (recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  safeTransferSelector ++ ((UInt256.ofNat recipient.toNat).toByteArray ++ amount.toByteArray)

theorem safeTransferCalldata_size (recipient : AccountAddress) (amount : UInt256) :
    (safeTransferCalldata recipient amount).size = 68 := by
  simp only [safeTransferCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem safeTransferEncode (recipient : AccountAddress) (amount : UInt256) :
    config.externalABI.encode? "transfer" [.address recipient, uint256Value amount] =
      some (safeTransferCalldata recipient amount) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0xa9059cbb).toBytesBE.drop 28).toArray)
    [abiAddress, abiUInt256] [.address recipient, uint256Value amount] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0xa9059cbb).toBytesBE.drop 28).toArray =
    safeTransferSelector from by decide +kernel]
  have hh : abiTupleHeadSize? [abiAddress, abiUInt256] = some 64 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, encodeAddressWord, encodeABIValue_uint256_word,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    List.toByteArray_append, byteArray_toList_toByteArray]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
