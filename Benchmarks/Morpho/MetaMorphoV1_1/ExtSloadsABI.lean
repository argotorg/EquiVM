import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon
import Reasoning.ABIViews

/-! ABI encoding of the singleton storage-read request passed to Morpho. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def extSloadsSelector : ByteArray := ⟨#[0x77, 0x84, 0xc6, 0x85]⟩

def extSloadsCalldata (slot : UInt256) : ByteArray :=
  extSloadsSelector ++ ((⟨32⟩ : UInt256).toByteArray ++
    ((⟨1⟩ : UInt256).toByteArray ++ slot.toByteArray))

theorem extSloadsCalldata_size (slot : UInt256) : (extSloadsCalldata slot).size = 100 := by
  simp only [extSloadsCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem extSloadsEncode (slot : UInt256) :
    config.externalABI.encode? "extSloads" [.array [wordBytes32Value slot]] =
      some (extSloadsCalldata slot) := by
  have hselector : ByteArray.mk ((EVM.Word.ofNat 0x7784c685).toBytesBE.drop 28).toArray =
      extSloadsSelector := by decide +kernel
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x7784c685).toBytesBE.drop 28).toArray)
    [.dynamicArray abiBytes32]
    [.array [wordBytes32Value slot]] = _
  rw [hselector]
  simp only [encodeCallWithSelector?,
    encodeABIValues_single_dynArray_static (elemTy := abiBytes32) (by rfl),
    encodeABIStaticArrayElems?, encodeABIValue_bytes32_word, bind, Option.bind,
    List.append_nil, List.length_cons, List.length_nil, Nat.zero_add]
  rw [List.toByteArray_append, List.toByteArray_append, natBytes_toByteArray,
    natBytes_toByteArray, byteArray_toList_toByteArray]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
