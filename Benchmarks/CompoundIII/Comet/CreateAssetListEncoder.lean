import Benchmarks.CompoundIII.Comet.ConstructorAssetReads
import Benchmarks.CompoundIII.Comet.CreationBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- The creation-code loop copies one canonical asset into the factory-call payload. -/
theorem cometCreateAssetListEncodeAsset {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {src dest entry index count start factory : UInt256} {a : ConstructorAsset} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hsrc : 96 ≤ src.toNat)
    (hin : src.toNat + 224 ≤ mem.size) (hdisj : src.toNat + 224 ≤ dest.toNat)
    (hbound : dest.toNat + 224 < UInt256.size)
    (hentry : memLoad entry mem = src)
    (hread : ∀ j, j < 7 → memLoad (src + UInt256.ofNat (32 * j)) mem = a.word j)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2075⟩
      (index :: count :: entry :: dest :: start :: factory :: start :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1358⟩
      ((UInt256.ofNat 1 + index) :: count :: (entry + UInt256.ofNat 32) ::
        (dest + UInt256.ofNat 224) :: start :: factory :: start :: R)
      (constructorAssetFieldMemory mem dest.toNat a 7) aw' rdata σ k' C' := by
  have hload (n j : Nat) (hj : j < 7) :
      memLoad (src + UInt256.ofNat (32 * j))
        (constructorAssetFieldMemory mem dest.toNat a n) = a.word j := by
    rw [memoryPrefix_load (constructorAssetFieldMemory_prefix _ _ _ _)
      (by rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega)
      (by rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega)
      (by rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega)]
    exact hread j hj
  have hm0 : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (a.word 0) = a.word 0 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
      (constructorAddressScalar_canonical a.asset)
  have hm1 : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (a.word 1) = a.word 1 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
      (constructorAddressScalar_canonical a.priceFeed)
  have hm2 : UInt256.land (UInt256.ofNat 255) (a.word 2) = a.word 2 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide)
      (constructorUintScalar_canonical ⟨8, by decide⟩ a.decimals)
  have hm64 (j : Nat) (hlo : 3 ≤ j) (hhi : j ≤ 5) : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      (a.word j) = a.word j := by
    rw [u256_land_comm]
    apply u256LandMaskCleanOfToNat (bits := 64) _ _ (by decide)
    interval_cases j <;> exact constructorUintScalar_canonical ⟨64, by decide⟩ _
  have hm6 : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
      (a.word 6) = a.word 6 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 128) _ _ (by decide)
      (constructorUintScalar_canonical ⟨128, by decide⟩ a.supplyCap)
  have hw0 := hload 0 0 (by decide)
  have hw1 := hload 1 1 (by decide)
  have hw2 := hload 2 2 (by decide)
  have hw3 := hload 3 3 (by decide)
  have hw4 := hload 4 4 (by decide)
  simp only [constructorAssetFieldMemory, Nat.reduceMul, Nat.add_zero,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right] at hw0 hw1 hw2 hw3 hw4
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  have hadd (off : Nat) (hoff : off ≤ 224) :
      (dest + UInt256.ofNat off).toNat = dest.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  obtain ⟨aw1, k1, C1, r1⟩ := cometWithExtendedAssetListCreation_block_2075_packed
    (by change R.length + 3 + 11 ≤ 1024; omega) h
  simp (disch := decide) only [cometWithExtendedAssetListCreation_block_2075_stack,
    cometWithExtendedAssetListCreation_block_2075_memory, hentry,
    u256_add_comm (UInt256.ofNat 32) src, hwrite, hadd, hw0, hm0, hw1, hm1,
    hw2, hm2, hw3, hm64, hw4] at r1
  change RD _ _ _ _ _
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
      a.word 4 :: UInt256.ofNat 128 ::
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
      UInt256.ofNat 32 :: src :: index :: count :: entry :: dest :: start :: factory :: start :: R)
    (constructorAssetFieldMemory mem dest.toNat a 4) _ _ _ _ _ at r1
  have hw5 := hload 5 5 (by decide)
  have hw6 := hload 6 6 (by decide)
  simp only [constructorAssetFieldMemory, Nat.reduceMul, Nat.add_zero] at hw5 hw6
  obtain ⟨aw2, k2, C2, r2⟩ := cometWithExtendedAssetListCreation_block_2150_packed
    (by omega) (by native_decide) r1
  simp (disch := decide) only [cometWithExtendedAssetListCreation_block_2150_stack,
    cometWithExtendedAssetListCreation_block_2150_memory,
    constructorAssetFieldMemory, Nat.reduceMul, Nat.add_zero, hwrite, hadd,
    hm64, hw5, u256_add_comm (UInt256.ofNat 192) src, hw6, hm6] at r2
  exact ⟨aw2, k2, C2, r2⟩

end Benchmarks.CompoundIII.Comet
