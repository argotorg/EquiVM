import Benchmarks.CompoundIII.Comet.AssetReads
import Benchmarks.CompoundIII.Comet.AssetStructMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem cometAssetChecks {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr dest ret : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hlo : 96 ≤ ptr.toNat)
    (hsize : ptr.toNat + 256 ≤ mem.size) (hdisj : ptr.toNat + 256 ≤ dest.toNat)
    (hbound : dest.toNat + 256 < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hword : ∀ off ≤ 224, memLoad (ptr + UInt256.ofNat off) mem = calldataWord out off)
    (h : RD (deployedRuntime v) ee g s0 ⟨7335⟩
      (ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) mem aw out σ k C) :
    if AssetCanonical out then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (dest :: R)
        (assetStore mem dest out 8) aw' out σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hr (n : Nat) (hn : n ≤ 8) (off : Nat) (ho : off ≤ 224) :
      memLoad (ptr + UInt256.ofNat off) (assetStore mem dest out n) = calldataWord out off := by
    have ha := uadd_word_ofNat_toNat ptr off (by omega)
    exact (memoryPrefix_load (assetStore_prefix hn hbound (Nat.le_refl _))
      (by rw [ha]; omega) (by rw [ha]; omega) (by rw [ha]; omega)).trans (hword off ho)
  have r0 := cometWithExtendedAssetList_block_7335
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hw0 := hr 0 (by decide) 0 (by decide)
  simp only [assetStore_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right] at hw0
  by_cases hc0 : (calldataWord out 0).toNat < 2^8
  swap
  · rw [if_neg (fun hc ↦ hc0 hc.1)]
    exact cometRead8_bad (v := v) (by change R.length + 5 + 6 ≤ 1024; omega)
      (by rw [hw0]; exact hc0) r0
  obtain ⟨aw1, k1, C1, d1⟩ := cometRead8_ok (v := v)
    (by change R.length + 5 + 6 ≤ 1024; omega)
    (by rw [hw0]; exact hc0)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r0
  change RD _ _ _ _ _ (memLoad ptr (assetStore mem dest out 0) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d1
  change memLoad ptr (assetStore mem dest out 0) = _ at hw0
  rw [hw0] at d1
  have r1 := cometWithExtendedAssetList_block_7344
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d1
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 32) :: ⟨7358⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (writeWord mem dest.toNat (calldataWord out 0)) _ _ _ _ _ at r1
  have hm1 : assetStore mem dest out 1 = writeWord mem dest.toNat (calldataWord out 0) := by
    rw [assetStore_succ, assetStore_zero]
    simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      uint256_add_zero_right]
  rw [← hm1] at r1
  have hw1 := hr 1 (by decide) 32 (by decide)
  by_cases hc1 : (calldataWord out 32).toNat < 2^160
  swap
  · rw [if_neg (fun hc ↦ hc1 hc.2.1)]
    exact cometReadAddress_bad (v := v) (by change R.length + 5 + 7 ≤ 1024; omega)
      (by rw [hw1]; exact hc1) r1
  obtain ⟨aw2, k2, C2, d2⟩ := cometReadAddress_ok (v := v)
    (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [hw1]; exact hc1)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 32) (assetStore mem dest out 1) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d2
  rw [hw1] at d2
  have r2 := cometWithExtendedAssetList_block_7358
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d2
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 64) :: ⟨7375⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 2) _ _ _ _ _ at r2
  have hw2 := hr 2 (by decide) 64 (by decide)
  by_cases hc2 : (calldataWord out 64).toNat < 2^160
  swap
  · rw [if_neg (fun hc ↦ hc2 hc.2.2.1)]
    exact cometReadAddress_bad (v := v) (by change R.length + 5 + 7 ≤ 1024; omega)
      (by rw [hw2]; exact hc2) r2
  obtain ⟨aw3, k3, C3, d3⟩ := cometReadAddress_ok (v := v)
    (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [hw2]; exact hc2)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 64) (assetStore mem dest out 2) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d3
  rw [hw2] at d3
  have r3 := cometWithExtendedAssetList_block_7375
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d3
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 96) :: ⟨7392⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 3) _ _ _ _ _ at r3
  have hw3 := hr 3 (by decide) 96 (by decide)
  by_cases hc3 : (calldataWord out 96).toNat < 2^64
  swap
  · rw [if_neg (fun hc ↦ hc3 hc.2.2.2.1)]
    exact cometRead64_bad (v := v) (by change R.length + 5 + 5 ≤ 1024; omega)
      (by rw [hw3]; exact hc3) r3
  obtain ⟨aw4, k4, C4, d4⟩ := cometRead64_ok (v := v)
    (by change R.length + 5 + 5 ≤ 1024; omega)
    (by rw [hw3]; exact hc3)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 96) (assetStore mem dest out 3) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d4
  rw [hw3] at d4
  have r4 := cometWithExtendedAssetList_block_7392
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d4
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 128) :: ⟨7409⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 4) _ _ _ _ _ at r4
  have hw4 := hr 4 (by decide) 128 (by decide)
  by_cases hc4 : (calldataWord out 128).toNat < 2^64
  swap
  · rw [if_neg (fun hc ↦ hc4 hc.2.2.2.2.1)]
    exact cometRead64_bad (v := v) (by change R.length + 5 + 5 ≤ 1024; omega)
      (by rw [hw4]; exact hc4) r4
  obtain ⟨aw5, k5, C5, d5⟩ := cometRead64_ok (v := v)
    (by change R.length + 5 + 5 ≤ 1024; omega)
    (by rw [hw4]; exact hc4)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 128) (assetStore mem dest out 4) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d5
  rw [hw4] at d5
  have r5 := cometWithExtendedAssetList_block_7409
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d5
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 160) :: ⟨7426⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 5) _ _ _ _ _ at r5
  have hw5 := hr 5 (by decide) 160 (by decide)
  by_cases hc5 : (calldataWord out 160).toNat < 2^64
  swap
  · rw [if_neg (fun hc ↦ hc5 hc.2.2.2.2.2.1)]
    exact cometRead64_bad (v := v) (by change R.length + 5 + 5 ≤ 1024; omega)
      (by rw [hw5]; exact hc5) r5
  obtain ⟨aw6, k6, C6, d6⟩ := cometRead64_ok (v := v)
    (by change R.length + 5 + 5 ≤ 1024; omega)
    (by rw [hw5]; exact hc5)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 160) (assetStore mem dest out 5) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d6
  rw [hw5] at d6
  have r6 := cometWithExtendedAssetList_block_7426
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d6
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 192) :: ⟨7443⟩ :: ptr ::
    ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 6) _ _ _ _ _ at r6
  have hw6 := hr 6 (by decide) 192 (by decide)
  by_cases hc6 : (calldataWord out 192).toNat < 2^64
  swap
  · rw [if_neg (fun hc ↦ hc6 hc.2.2.2.2.2.2.1)]
    exact cometRead64_bad (v := v) (by change R.length + 5 + 5 ≤ 1024; omega)
      (by rw [hw6]; exact hc6) r6
  obtain ⟨aw7, k7, C7, d7⟩ := cometRead64_ok (v := v)
    (by change R.length + 5 + 5 ≤ 1024; omega)
    (by rw [hw6]; exact hc6)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 192) (assetStore mem dest out 6) ::
    ptr :: ⟨224⟩ :: ⟨7454⟩ :: dest :: ret :: R) _ _ _ _ _ _ at d7
  rw [hw6] at d7
  have r7 := cometWithExtendedAssetList_block_7443
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) d7
  change RD _ _ _ _ _ ((ptr + UInt256.ofNat 224) :: ⟨7454⟩ :: dest :: ret :: R)
    (assetStore mem dest out 7) _ _ _ _ _ at r7
  have hw7 := hr 7 (by decide) 224 (by decide)
  by_cases hc7 : (calldataWord out 224).toNat < 2^128
  swap
  · rw [if_neg (fun hc ↦ hc7 hc.2.2.2.2.2.2.2)]
    exact cometRead128_bad (v := v) (by change R.length + 2 + 5 ≤ 1024; omega)
      (by rw [hw7]; exact hc7) r7
  obtain ⟨aw8, k8, C8, d8⟩ := cometRead128_ok (v := v)
    (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [hw7]; exact hc7)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
  change RD _ _ _ _ _ (memLoad (ptr + UInt256.ofNat 224)
    (assetStore mem dest out 7) :: dest :: ret :: R) _ _ _ _ _ _ at d8
  rw [hw7] at d8
  have r8 := cometWithExtendedAssetList_block_7454
    (immWords := wordsOf (immStore v))
    (by change R.length + 0 + 5 ≤ 1024; omega)
    hret d8
  change RD _ _ _ _ _ (dest :: R)
    (assetStore mem dest out 8) _ _ _ _ _ at r8
  rw [if_pos ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩]
  exact ⟨_, _, _, r8⟩

end Benchmarks.CompoundIII.Comet
