import Benchmarks.CompoundIII.Comet.AssetResultMemory
import Benchmarks.CompoundIII.Comet.AssetEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometAssetEncoder {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {src dest ret : UInt256} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hlo : 96 ≤ src.toNat)
    (hsize : src.toNat + 256 ≤ mem.size) (hdisj : src.toNat + 256 ≤ dest.toNat)
    (hbound : dest.toNat + 256 < UInt256.size) (hc : AssetCanonical out)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hword : ∀ j < 8, memLoad (src + UInt256.ofNat (32 * j)) mem = calldataWord out (32 * j))
    (h : RD (deployedRuntime v) ee g s0 ⟨2971⟩ (dest :: src :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret ((dest + ⟨256⟩) :: R)
      (assetStore mem dest out 8) aw' rdata σ k' C' := by
  have hr (n : Nat) (hn : n ≤ 8) (j : Nat) (hj : j < 8) :
      memLoad (src + UInt256.ofNat (32 * j)) (assetStore mem dest out n) =
        calldataWord out (32 * j) := by
    have ha := uadd_word_ofNat_toNat src (32 * j) (by omega)
    exact (memoryPrefix_load (assetStore_prefix hn hbound (Nat.le_refl _))
      (by rw [ha]; omega) (by rw [ha]; omega) (by rw [ha]; omega)).trans (hword j hj)
  have hm0 : UInt256.land (calldataWord out 0) (UInt256.ofNat 255) = calldataWord out 0 :=
    lowByteClean hc.1
  have hm1 : UInt256.land (calldataWord out 32) solcAddrMask = calldataWord out 32 :=
    solcAddrMask_clean hc.2.1
  have hm2 : UInt256.land (calldataWord out 64) solcAddrMask = calldataWord out 64 :=
    solcAddrMask_clean hc.2.2.1
  have hm3 : UInt256.land (calldataWord out 96) assetMask64 = calldataWord out 96 :=
    u256LandMaskCleanOfToNat _ _ (by decide : assetMask64.toNat = 2^64 - 1) hc.2.2.2.1
  have hm4 : UInt256.land assetMask64 (calldataWord out 128) = calldataWord out 128 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (by decide : assetMask64.toNat = 2^64 - 1) hc.2.2.2.2.1
  have hm5 : UInt256.land assetMask64 (calldataWord out 160) = calldataWord out 160 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (by decide : assetMask64.toNat = 2^64 - 1) hc.2.2.2.2.2.1
  have hm6 : UInt256.land assetMask64 (calldataWord out 192) = calldataWord out 192 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (by decide : assetMask64.toNat = 2^64 - 1) hc.2.2.2.2.2.2.1
  have hm7 : UInt256.land assetMask128 (calldataWord out 224) = calldataWord out 224 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (by decide : assetMask128.toNat = 2^128 - 1)
      hc.2.2.2.2.2.2.2
  have hw0 := hr 0 (by decide) 0 (by decide)
  simp only [assetStore_zero, Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right] at hw0
  have hw1 := hr 1 (by decide) 1 (by decide)
  have hw2 := hr 2 (by decide) 2 (by decide)
  have hw3 := hr 3 (by decide) 3 (by decide)
  have hw4 := hr 4 (by decide) 4 (by decide)
  rw [assetStore_one] at hw1
  rw [assetStore_succ _ _ _ 1, assetStore_one] at hw2
  rw [assetStore_succ _ _ _ 2, assetStore_succ _ _ _ 1, assetStore_one] at hw3
  rw [assetStore_succ _ _ _ 3, assetStore_succ _ _ _ 2,
    assetStore_succ _ _ _ 1, assetStore_one] at hw4
  simp only [Reasoning.Theory.writeWord, Nat.reduceMul] at hw1 hw2 hw3 hw4
  have r1 := cometWithExtendedAssetList_block_2971
    (immWords := wordsOf (immStore v)) (by omega) h
  simp only [cometWithExtendedAssetList_block_2971_stack,
    cometWithExtendedAssetList_block_2971_memory, hw0, hm0, hw1,
    show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask from rfl, hm1, hw2, hm2, hw3,
    show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = assetMask64 from rfl, hm3, hw4] at r1
  have hmem4 : assetStore mem dest out 4 = _ :=
    (assetStore_succ mem dest out 3).trans (by
      rw [assetStore_succ _ _ _ 2, assetStore_succ _ _ _ 1, assetStore_one])
  simp only [Reasoning.Theory.writeWord, Nat.reduceMul] at hmem4
  rw [← hmem4] at r1
  have r2 := cometWithExtendedAssetList_block_3055
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [cometWithExtendedAssetList_block_3055_memory,
    show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = assetMask64 from rfl, hm4] at r2
  change RD _ _ _ _ _ (src :: UInt256.ofNat 224 :: UInt256.ofNat 224 :: dest :: ⟨3121⟩ :: ret ::
    (dest + ⟨256⟩) :: R) (writeWord (assetStore mem dest out 4)
      (dest + UInt256.ofNat 128).toNat (calldataWord out 128)) _ _ _ _ _ at r2
  rw [← assetStore_succ mem dest out 4] at r2
  have hw5 := hr 5 (by decide) 5 (by decide)
  have hw6 := hr 6 (by decide) 6 (by decide)
  have hw7 := hr 7 (by decide) 7 (by decide)
  rw [assetStore_succ _ _ _ 5] at hw6
  rw [assetStore_succ _ _ _ 6, assetStore_succ _ _ _ 5] at hw7
  simp only [Reasoning.Theory.writeWord, Nat.reduceMul] at hw5 hw6 hw7
  have r3 := cometWithExtendedAssetList_block_3067
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [cometWithExtendedAssetList_block_3067_memory,
    u256_add_comm (UInt256.ofNat 160) src, u256_add_comm (UInt256.ofNat 192) src,
    hw5, show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = assetMask64 from rfl, hm5, hw6, hm6, hw7,
    show UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = assetMask128 from rfl, hm7] at r3
  have hmem8 : assetStore mem dest out 8 = _ :=
    (assetStore_succ mem dest out 7).trans (by
      rw [assetStore_succ _ _ _ 6, assetStore_succ _ _ _ 5])
  simp only [Reasoning.Theory.writeWord, Nat.reduceMul] at hmem8
  rw [← hmem8] at r3
  have r4 := cometWithExtendedAssetList_block_3121
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r3
  exact ⟨_, _, _, r4⟩

end Benchmarks.CompoundIII.Comet
