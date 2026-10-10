import Benchmarks.Morpho.MetaMorphoV1_1.StructAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SingleWordCallMemory

/-! The fixed-size input memory and ABI request of `idToMarketParams`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketParamsSelector : ByteArray := ⟨#[0x2c, 0x3c, 0x91, 0x57]⟩

def marketParamsSelectorWord : UInt256 := UInt256.shiftLeft ⟨742166871⟩ ⟨224⟩

def marketParamsCalldata (id : UInt256) : ByteArray := marketParamsSelector ++ id.toByteArray

theorem marketParamsCalldata_size (id : UInt256) : (marketParamsCalldata id).size = 36 := by
  simp only [marketParamsCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem marketParamsEncode (id : UInt256) :
    config.externalABI.encode? "idToMarketParams" [wordBytes32Value id] =
      some (marketParamsCalldata id) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x2c3c9157).toBytesBE.drop 28).toArray)
    [abiBytes32] [wordBytes32Value id] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x2c3c9157).toBytesBE.drop 28).toArray =
    marketParamsSelector from by decide +kernel]
  exact singleWordCallEncode marketParamsSelector id

def marketParamsCallMem (mem : ByteArray) (ptr : Nat) (id : UInt256) : ByteArray :=
  writeCascade mem [(ptr, marketParamsSelectorWord), (ptr + 4, id)]

theorem marketParamsCallMem_size (mem : ByteArray) (ptr : Nat) (id : UInt256) :
    (marketParamsCallMem mem ptr id).size = max mem.size (ptr + 36) :=
  singleWordCallMem_size mem ptr marketParamsSelectorWord id

theorem marketParamsCallMem_read (mem : ByteArray) (ptr : Nat) (id : UInt256) :
    (marketParamsCallMem mem ptr id).readWithPadding ptr 36 = marketParamsCalldata id := by
  simpa only [show marketParamsSelectorWord.toByteArray.extract 0 4 =
    marketParamsSelector from by decide +kernel] using
      singleWordCallMem_read mem ptr marketParamsSelectorWord id

def zeroStruct160Mem (mem : ByteArray) (ptr : Nat) : ByteArray :=
  writeCascade mem [(ptr, ⟨0⟩), (ptr + 32, ⟨0⟩), (ptr + 64, ⟨0⟩),
    (ptr + 96, ⟨0⟩), (ptr + 128, ⟨0⟩)]

theorem zeroStruct160Mem_size (mem : ByteArray) (ptr : Nat) :
    (zeroStruct160Mem mem ptr).size = max mem.size (ptr + 160) := by
  simp only [zeroStruct160Mem, writeCascade_cons, writeCascade_nil, writeWord_sparse_size]
  omega

theorem zeroStruct160Mem_free (mem : ByteArray) (ptr : Nat)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr) :
    memLoad ⟨64⟩ (zeroStruct160Mem mem ptr) = memLoad ⟨64⟩ mem := by
  have hread : (zeroStruct160Mem mem ptr).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
    apply sparseCascade_read_below _ _ _ hin
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega
  simp only [memLoad]
  rw [if_neg (by change ¬ 64 ≥ (zeroStruct160Mem mem ptr).size
                 rw [zeroStruct160Mem_size]; omega), if_neg (by change ¬ 64 ≥ mem.size; omega)]
  exact congrArg (fun data ↦ UInt256.ofNat (fromByteArrayBigEndian data)) hread

def marketParamsInitialMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  zeroStruct160Mem (writeWord mem 64 (nextCursor ptr ⟨160⟩)) ptr.toNat

theorem marketParamsInitialMem_free (mem : ByteArray) (ptr : UInt256) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (marketParamsInitialMem mem ptr) = nextCursor ptr ⟨160⟩ := by
  rw [marketParamsInitialMem, zeroStruct160Mem_free _ _ (by rw [writeWord_sparse_size]; omega)
    hlo]
  exact loadedWord_of_read (by change 64 + 32 ≤ _; rw [writeWord_sparse_size]; omega)
    (writeWord_sparse_read_back _ _ _)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
