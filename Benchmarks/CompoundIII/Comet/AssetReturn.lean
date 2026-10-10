import Benchmarks.CompoundIII.Comet.AssetEncoderEvm
import Benchmarks.CompoundIII.Comet.AssetMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def getAssetInfoMemory (i : UInt256) (out : ByteArray) : ByteArray :=
  assetResultMemory (assetZeroMemory solcFreePtrMem ⟨128⟩) ⟨384⟩ i out

theorem getAssetInfoMemory_free (i : UInt256) (out : ByteArray) :
    memLoad ⟨64⟩ (getAssetInfoMemory i out) = ⟨896⟩ :=
  assetResultMemory_free (by decide) (by decide)

theorem getAssetInfoMemory_size (i : UInt256) (out : ByteArray)
    (hlo : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (getAssetInfoMemory i out).size = 896 := by
  rw [getAssetInfoMemory, assetResultMemory_size (by decide) (by decide) hlo hhi,
    assetZeroMemory_size (by decide) (by decide), solcFreePtrMem_size]
  rfl

theorem getAssetInfoMemory_word (i : UInt256) (out : ByteArray) (j : Nat) (hj : j < 8) :
    memLoad (⟨640⟩ + UInt256.ofNat (32 * j)) (getAssetInfoMemory i out) =
      calldataWord out (32 * j) :=
  assetResultMemory_word (ptr := ⟨384⟩) (i := i)
    (mem := assetZeroMemory solcFreePtrMem ⟨128⟩) j hj (by decide)

theorem cometAssetPublicReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {out mem rdata : ByteArray}
    {aw ptr free : UInt256} {σ : AccountMap} {k C : Nat}
    (hv : AssetCanonical out) (hm : AssetMemory mem ptr free out)
    (h : RD (deployedRuntime v) ee g s0 ⟨3164⟩ [ptr, ⟨2570⟩]
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (wordBytes (assetWords out)) := by
  have r1 := cometWithExtendedAssetList_block_3164
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hf : memLoad (UInt256.ofNat 64) mem = free := hm.freeWord
  simp only [cometWithExtendedAssetList_block_3164_stack, hf] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAssetEncoder (v := v)
    (by change 15 ≤ 1024; decide) hm.lower hm.present hm.separate hm.bounded hv
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hm.words r1
  have r3 := cometWithExtendedAssetList_block_2570
    (immWords := wordsOf (immStore v)) (by change 3 ≤ 1024; decide) r2
  rw [word_add_sub_left] at r3
  have hr : (assetStore mem free out 8).readWithPadding free.toNat 256 =
      wordBytes (assetWords out) := assetStore_read (by decide) (by decide) hm.bounded
  exact hr ▸ r3

theorem cometGetAssetInfoReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {out : ByteArray} {aw i : UInt256}
    {σ : AccountMap} {k C : Nat} (hv : AssetValid out) (hhi : out.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨3164⟩ [⟨640⟩, ⟨2570⟩]
      (getAssetInfoMemory i out) aw out σ k C) :
    RDret (deployedRuntime v) g s0 σ (wordBytes (assetWords out)) := by
  exact cometAssetPublicReturn (v := v) hv.2 (free := ⟨896⟩)
    ⟨by decide, by rw [getAssetInfoMemory_size i out hv.1 hhi]; decide,
      by decide, by decide, getAssetInfoMemory_free i out, getAssetInfoMemory_word i out⟩ h

end Benchmarks.CompoundIII.Comet
