import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsMemory
import Reasoning.ABIViews

/-! Shared memory and ABI facts for an external call with one bytes32 argument. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def singleWordCallMem (mem : ByteArray) (ptr : Nat) (selector id : UInt256) : ByteArray :=
  writeCascade mem [(ptr, selector), (ptr + 4, id)]

theorem singleWordCallMem_size (mem : ByteArray) (ptr : Nat) (selector id : UInt256) :
    (singleWordCallMem mem ptr selector id).size = max mem.size (ptr + 36) := by
  simp only [singleWordCallMem, writeCascade_cons, writeCascade_nil, writeWord_sparse_size]
  omega

theorem singleWordCallMem_read (mem : ByteArray) (ptr : Nat) (selector id : UInt256) :
    (singleWordCallMem mem ptr selector id).readWithPadding ptr 36 =
      selector.toByteArray.extract 0 4 ++ id.toByteArray := by
  have hu := lt_usize 0 (by decide)
  have hs : (singleWordCallMem mem ptr selector id).readWithPadding ptr 4 =
      selector.toByteArray.extract 0 4 := by
    have h := sparseCascade_read_window mem ptr 0 4 selector [(ptr + 4, id)]
      (by simp only [WindowDisjointFromWrites]
          exact ⟨by omega, .inl ⟨by omega, by omega⟩, trivial⟩)
      (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add] using h
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 4 32 (by decide) (by decide)
      (by rw [singleWordCallMem_size]; omega), hs]
  change selector.toByteArray.extract 0 4 ++
    (writeWord (writeWord mem ptr selector) (ptr + 4) id).readWithPadding (ptr + 4) 32 = _
  rw [writeWord_sparse_read_back]

theorem singleWordCallEncode (selector : ByteArray) (id : UInt256) :
    encodeCallWithSelector? selector [abiBytes32] [wordBytes32Value id] =
      some (selector ++ id.toByteArray) := by
  simp only [encodeCallWithSelector?, encodeABIValues?, encodeABIValuesFrom?,
    encodeABIValue_bytes32_word,
    show abiTupleHeadSize? [abiBytes32] = some 32 from by
      simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiBytes32],
    show isDynamicABIType abiBytes32 = false from rfl, bind, Option.bind,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    byteArray_toList_toByteArray]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
