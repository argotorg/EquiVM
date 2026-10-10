import Benchmarks.CompoundIII.Comet.ReentrancyModel
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_056
import Benchmarks.CompoundIII.Comet.MappingScratch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

theorem reentrancyCode_size (v : CometWithExtendedAssetListImmutables) :
    (deployedRuntime v).size = 18599 :=
  (Layout.runtime_size_of_bounds (words := wordsOf (immStore v)) immutableLayout_inBounds).trans
    (by native_decide)

theorem reentrancyCode_read (v : CometWithExtendedAssetListImmutables) :
    (deployedRuntime v).readWithPadding 18514 32 = reentrancySlot.toByteArray := by
  change (immutableLayout.runtime cometWithExtendedAssetListBytecode
    (wordsOf (immStore v))).readWithPadding 18514 32 = _
  rw [← Layout.runtimeN_eq_runtime (Layout.widths32_of_inBounds immutableLayout_inBounds)]
  rw [Layout.runtimeN_read_preserved 18514 32
    (Layout.inBoundsN_of_inBounds immutableLayout_inBounds)
    (by native_decide) (by native_decide) (by decide) (by decide)]
  native_decide

def reentrancyCopyMemory (v : CometWithExtendedAssetListImmutables) (mem : ByteArray) : ByteArray :=
  (deployedRuntime v).write 18514 mem 0 32

def reentrancyMemory (v : CometWithExtendedAssetListImmutables) (mem : ByteArray) : ByteArray :=
  writeWord (reentrancyCopyMemory v mem) 0 (memLoad ⟨0⟩ mem)

theorem reentrancyCopyMemory_size (v : CometWithExtendedAssetListImmutables) (mem : ByteArray) :
    (reentrancyCopyMemory v mem).size = max mem.size 32 :=
  copyWindow_size _ _ 18514 0 32 (by decide) (by rw [reentrancyCode_size]; decide) (by omega)

theorem reentrancyCopyMemory_word (v : CometWithExtendedAssetListImmutables) (mem : ByteArray) :
    memLoad (UInt256.ofNat 0) (reentrancyCopyMemory v mem) = reentrancySlot := by
  apply loadedWord_of_read
  · rw [reentrancyCopyMemory_size]; exact Nat.le_max_right _ _
  · have hr := copyWindow_read_word (deployedRuntime v) mem 18514 0 32 0
      (by decide) (by rw [reentrancyCode_size]; decide) (by omega) (by decide)
    exact hr.trans (reentrancyCode_read v)

theorem reentrancyMemory_size (v : CometWithExtendedAssetListImmutables) (mem : ByteArray)
    (hm : 32 ≤ mem.size) : (reentrancyMemory v mem).size = mem.size := by
  rw [reentrancyMemory, writeWord_sparse_size, reentrancyCopyMemory_size]
  omega

theorem reentrancyMemory_free (v : CometWithExtendedAssetListImmutables) (mem : ByteArray)
    (hm : 96 ≤ mem.size) : memLoad ⟨64⟩ (reentrancyMemory v mem) = memLoad ⟨64⟩ mem := by
  have hs := reentrancyMemory_size v mem (by omega)
  have hc := reentrancyCopyMemory_size v mem
  have hr : (reentrancyMemory v mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
    rw [reentrancyMemory, writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by omega⟩)]
    exact copyWindow_read_preserved _ _ 18514 0 32 64
      (by decide) (by rw [reentrancyCode_size]; decide) (by omega) hm (Or.inr (by decide))
  unfold memLoad
  rw [hs, if_neg (by change ¬ mem.size ≤ 64; omega)]
  change UInt256.ofNat (fromByteArrayBigEndian ((reentrancyMemory v mem).readWithPadding 64 32)) = _
  rw [hr]
  rw [if_neg (by change ¬ mem.size ≤ 64; omega)]
  rfl

end Benchmarks.CompoundIII.Comet
