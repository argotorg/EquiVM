import Benchmarks.CompoundIII.Comet.AssetCallMemory
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def assetZeroMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeCascade mem [
    (64, ptr + ⟨256⟩),
    (ptr.toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 32).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 64).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 96).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 128).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 160).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 192).toNat, ⟨0⟩),
    ((ptr + UInt256.ofNat 224).toNat, ⟨0⟩)]

theorem assetZeroMemory_size {mem : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 256 < UInt256.size) :
    (assetZeroMemory mem ptr).size = max mem.size (ptr.toNat + 256) := by
  have ha (off : Nat) (ho : off ≤ 224) :
      (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  simp only [assetZeroMemory, writeCascade, writeWord_sparse_size,
    ha 32 (by decide), ha 64 (by decide), ha 96 (by decide), ha 128 (by decide),
    ha 160 (by decide), ha 192 (by decide), ha 224 (by decide)]
  omega

theorem assetZeroMemory_free {mem : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hb : ptr.toNat + 256 < UInt256.size) :
    memLoad ⟨64⟩ (assetZeroMemory mem ptr) = ptr + ⟨256⟩ := by
  have ha (off : Nat) (ho : off ≤ 224) :
      (ptr + UInt256.ofNat off).toNat = ptr.toNat + off :=
    uadd_word_ofNat_toNat ptr off (by omega)
  apply loadedWord_of_read
  · rw [assetZeroMemory_size hlo hb]; change 64 + 32 ≤ _; omega
  · rw [assetZeroMemory, writeCascade_cons]
    change ByteArray.readWithPadding _ 64 32 = _
    rw [sparseCascade_read_below _ _ 64
      (by rw [writeWord_sparse_size]; omega) (by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp only [Prod.fst, ha 32 (by decide), ha 64 (by decide), ha 96 (by decide),
            ha 128 (by decide), ha 160 (by decide), ha 192 (by decide), ha 224 (by decide)]
          omega)]
    exact writeWord_sparse_read_back _ _ _

theorem cometAllocateAssetZero {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hptr : ptr.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7039⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (ptr :: R)
      (assetZeroMemory mem ptr) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7039
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_7039_stack,
    show memLoad (UInt256.ofNat 64) mem = ptr from hfree] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocateBounded (v := v) (bound := 8)
    (by change R.length + 2 + 6 ≤ 1024; omega) (by decide) hptr
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  rw [show allocationEnd ptr (UInt256.ofNat 256) = ptr + ⟨256⟩ from allocationEnd_256 ptr] at r2
  have r3 := cometWithExtendedAssetList_block_7055
    (immWords := wordsOf (immStore v)) hstack hret r2
  exact ⟨_, _, _, r3⟩

end Benchmarks.CompoundIII.Comet
