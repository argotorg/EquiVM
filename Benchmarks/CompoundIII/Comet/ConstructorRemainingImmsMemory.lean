import Benchmarks.CompoundIII.Comet.ConstructorScaleEvm
import Benchmarks.CompoundIII.Comet.AssetCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorMask64 : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)

def constructorMask104 : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1)

theorem constructorRecordWord_uint104Canonical (c : ConstructorConfig) {j : Nat}
    (hlo : 17 ≤ j) (hhi : j < 20) : (constructorRecordWord c j).toNat < 2^104 := by
  interval_cases j <;> exact constructorUintScalar_canonical ⟨104, by decide⟩ _

theorem constructorRecordWord_clean64 (c : ConstructorConfig) {j : Nat}
    (hlo : 5 ≤ j) (hhi : j < 17) :
    UInt256.land constructorMask64 (constructorRecordWord c j) = constructorRecordWord c j := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
    (constructorRecordWord_uint64Canonical c hlo hhi)

theorem constructorRecordWord_clean104 (c : ConstructorConfig) {j : Nat}
    (hlo : 17 ≤ j) (hhi : j < 20) :
    UInt256.land constructorMask104 (constructorRecordWord c j) = constructorRecordWord c j := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 104) _ _ (by native_decide)
    (constructorRecordWord_uint104Canonical c hlo hhi)

def constructorRateWord (c : ConstructorConfig) (j : Nat) : UInt256 :=
  UInt256.div (constructorRecordWord c j) (UInt256.ofNat 31536000)

theorem constructorRateWord_clean (c : ConstructorConfig) {j : Nat}
    (hlo : 5 ≤ j) (hhi : j < 17) :
    UInt256.land constructorMask64 (constructorRateWord c j) = constructorRateWord c j := by
  rw [u256_land_comm]
  apply u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
  exact lt_of_le_of_lt (Nat.div_le_self _ _)
    (constructorRecordWord_uint64Canonical c hlo hhi)

theorem constructorScaleMemory_scale (c : ConstructorConfig) (w : UInt256) (mem : ByteArray) :
    memLoad (UInt256.ofNat 576) (constructorScaleMemory c w mem) = constructorScaleWord w := by
  unfold constructorScaleMemory
  rw [memLoad_writeWord_preserved _ _ _ _ (by
    rw [writeWord_sparse_size]
    change 608 ≤ max mem.size 608
    exact Nat.le_max_right _ _) (Or.inl (by decide))]
  exact memLoad_writeWord_self _ (UInt256.ofNat 576) _

def constructorRewardMemory (c : ConstructorConfig) (w : UInt256) (mem : ByteArray) : ByteArray :=
  let mem := writeWord mem 864 (UInt256.div (constructorScaleWord w) (UInt256.ofNat 1000000))
  let mem := writeWord mem 704 (constructorRecordWord c 17)
  let mem := writeWord mem 640 (constructorRecordWord c 15)
  let mem := writeWord mem 672 (constructorRecordWord c 16)
  writeWord mem 736 (constructorRecordWord c 18)

def constructorRewardStack (c : ConstructorConfig) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat 768 :: constructorRecordWord c 19 :: constructorMask64 :: UInt256.ofNat 480 ::
    UInt256.ofNat 640 :: UInt256.ofNat 512 :: UInt256.ofNat (constructorRecordBase c) :: R

theorem constructorRewardMemory_data {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem) (w : UInt256) :
    ConstructorDataMemory c (constructorRewardMemory c w mem) := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  unfold constructorRewardMemory
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  exact hm.writeBelow _ (by omega)

theorem constructorReward_eq {c : ConstructorConfig} {w : UInt256} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem)
    (hscale : memLoad (UInt256.ofNat 576) mem = constructorScaleWord w)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1024_stack (mem := mem)
      (x0 := UInt256.ofNat (constructorRecordBase c)) (R := R) = constructorRewardStack c R ∧
    cometWithExtendedAssetListCreation_block_1024_memory (mem := mem)
      (x0 := UInt256.ofNat (constructorRecordBase c)) = constructorRewardMemory c w mem := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  have h1 := hm.writeBelow
    (UInt256.div (constructorScaleWord w) (UInt256.ofNat 1000000)) (off := 864) (by omega)
  have h2 := h1.writeBelow (constructorRecordWord c 17) (off := 704) (by omega)
  have h3 := h2.writeBelow (constructorRecordWord c 15) (off := 640) (by omega)
  have h4 := h3.writeBelow (constructorRecordWord c 16) (off := 672) (by omega)
  have h5 := h4.writeBelow (constructorRecordWord c 18) (off := 736) (by omega)
  have hr1 := h1.scalar (j := 17) (by decide) hsize
  have hr2 := h2.scalar (j := 15) (by decide) hsize
  have hr3 := h3.scalar (j := 16) (by decide) hsize
  have hr4 := h4.scalar (j := 18) (by decide) hsize
  have hr5 := h5.scalar (j := 19) (by decide) hsize
  simp only [Nat.reduceMul] at hr1 hr2 hr3 hr4 hr5
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  have h64 := @constructorRecordWord_clean64 c
  have h104 := @constructorRecordWord_clean104 c
  unfold constructorMask64 at h64
  unfold constructorMask104 at h104
  unfold cometWithExtendedAssetListCreation_block_1024_stack
    cometWithExtendedAssetListCreation_block_1024_memory
  simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hwrite, hscale,
    hr1, h104, hr2, h64, hr3, hr4, hr5]
  exact ⟨rfl, rfl⟩

def constructorSupplyMemory (c : ConstructorConfig) (mem : ByteArray) : ByteArray :=
  let mem := writeWord mem 768 (constructorRecordWord c 19)
  let mem := writeWord mem 288 (constructorRecordWord c 5)
  let mem := writeWord mem 320 (constructorRateWord c 6)
  let mem := writeWord mem 352 (constructorRateWord c 7)
  writeWord mem 384 (constructorRateWord c 8)

def constructorSupplyStack (c : ConstructorConfig) (R : List UInt256) : List UInt256 :=
  constructorMask64 :: constructorRecordWord c 9 :: UInt256.ofNat 256 :: UInt256.ofNat 352 ::
    UInt256.ofNat 320 :: UInt256.ofNat 31536000 :: UInt256.ofNat 384 :: constructorMask64 ::
    UInt256.ofNat 480 :: UInt256.ofNat 640 :: UInt256.ofNat 512 ::
    UInt256.ofNat (constructorRecordBase c) :: R

theorem constructorSupplyMemory_data {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem) :
    ConstructorDataMemory c (constructorSupplyMemory c mem) := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  unfold constructorSupplyMemory
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  exact hm.writeBelow _ (by omega)

theorem constructorSupply_eq {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1119_stack (mem := mem)
      (x0 := UInt256.ofNat 768) (x1 := constructorRecordWord c 19) (x2 := constructorMask64)
      (x3 := UInt256.ofNat 480) (x4 := UInt256.ofNat 640) (x5 := UInt256.ofNat 512)
      (x6 := UInt256.ofNat (constructorRecordBase c)) (R := R) = constructorSupplyStack c R ∧
    cometWithExtendedAssetListCreation_block_1119_memory (mem := mem)
      (x0 := UInt256.ofNat 768) (x1 := constructorRecordWord c 19) (x2 := constructorMask64)
      (x6 := UInt256.ofNat (constructorRecordBase c)) = constructorSupplyMemory c mem := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  have h1 := hm.writeBelow (constructorRecordWord c 19) (off := 768) (by omega)
  have h2 := h1.writeBelow (constructorRecordWord c 5) (off := 288) (by omega)
  have h3 := h2.writeBelow (constructorRateWord c 6) (off := 320) (by omega)
  have h4 := h3.writeBelow (constructorRateWord c 7) (off := 352) (by omega)
  have h5 := h4.writeBelow (constructorRateWord c 8) (off := 384) (by omega)
  have hr1 := h1.scalar (j := 5) (by decide) hsize
  have hr2 := h2.scalar (j := 6) (by decide) hsize
  have hr3 := h3.scalar (j := 7) (by decide) hsize
  have hr4 := h4.scalar (j := 8) (by decide) hsize
  have hr5 := h5.scalar (j := 9) (by decide) hsize
  simp only [Nat.reduceMul] at hr1 hr2 hr3 hr4 hr5
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  have hrate (j : Nat) : UInt256.div (constructorRecordWord c j) (UInt256.ofNat 31536000) =
      constructorRateWord c j := rfl
  unfold cometWithExtendedAssetListCreation_block_1119_stack
    cometWithExtendedAssetListCreation_block_1119_memory
  simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hwrite, hr1, hr2, hr3, hr4, hr5,
    constructorRecordWord_clean64, hrate, constructorRateWord_clean]
  exact ⟨rfl, rfl⟩

def constructorBorrowMemory (c : ConstructorConfig) (mem : ByteArray) : ByteArray :=
  let mem := writeWord mem 416 (constructorRecordWord c 9)
  let mem := writeWord mem 448 (constructorRateWord c 10)
  let mem := writeWord mem 480 (constructorRateWord c 11)
  let mem := writeWord mem 512 (constructorRateWord c 12)
  writeWord mem 832 (UInt256.ofNat c.assetConfigs.length)

theorem constructorBorrowMemory_data {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem) :
    ConstructorDataMemory c (constructorBorrowMemory c mem) := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  unfold constructorBorrowMemory
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  exact hm.writeBelow _ (by omega)

def constructorFactorySelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 235428955) (UInt256.ofNat 227)

def constructorFactoryMemory (c : ConstructorConfig) (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  writeWord (constructorBorrowMemory c mem) ptr.toNat constructorFactorySelectorWord

theorem constructorFactorySetup_eq {c : ConstructorConfig} {mem : ByteArray}
    {delegate ptr : UInt256} (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hn : c.assetConfigs.length ≤ 24)
    (hdelegate : memLoad (UInt256.ofNat 256) (constructorBorrowMemory c mem) = delegate)
    (hptr : memLoad (UInt256.ofNat 64) (constructorBorrowMemory c mem) = ptr) (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1200_stack (mem := mem)
      (x0 := constructorMask64) (x1 := constructorRecordWord c 9) (x2 := UInt256.ofNat 256)
      (x3 := UInt256.ofNat 352) (x4 := UInt256.ofNat 320) (x5 := UInt256.ofNat 31536000)
      (x6 := UInt256.ofNat 384) (x7 := constructorMask64) (x8 := UInt256.ofNat 480)
      (x9 := UInt256.ofNat 640) (x10 := UInt256.ofNat 512)
      (x11 := UInt256.ofNat (constructorRecordBase c)) (R := R) =
        delegate :: UInt256.ofNat 4 :: ptr :: UInt256.ofNat 32 ::
          UInt256.ofNat (constructorRecordBase c) :: ptr :: R ∧
    cometWithExtendedAssetListCreation_block_1200_memory (mem := mem)
      (x0 := constructorMask64) (x1 := constructorRecordWord c 9)
      (x3 := UInt256.ofNat 352) (x4 := UInt256.ofNat 320) (x5 := UInt256.ofNat 31536000)
      (x6 := UInt256.ofNat 384) (x7 := constructorMask64) (x8 := UInt256.ofNat 480)
      (x9 := UInt256.ofNat 640) (x10 := UInt256.ofNat 512)
      (x11 := UInt256.ofNat (constructorRecordBase c)) = constructorFactoryMemory c ptr mem := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  have h1 := hm.writeBelow (constructorRecordWord c 9) (off := 416) (by omega)
  have h2 := h1.writeBelow (constructorRateWord c 10) (off := 448) (by omega)
  have h3 := h2.writeBelow (constructorRateWord c 11) (off := 480) (by omega)
  have h4 := h3.writeBelow (constructorRateWord c 12) (off := 512) (by omega)
  have hr1 := h1.scalar (j := 10) (by decide) hsize
  have hr2 := h2.scalar (j := 11) (by decide) hsize
  have hr3 := h3.scalar (j := 12) (by decide) hsize
  have hr4 := h4.assets hsize
  have hr5 := h4.assetCount hsize
  simp only [Nat.reduceMul] at hr1 hr2 hr3
  have hnclean : UInt256.land (UInt256.ofNat 255) (UInt256.ofNat c.assetConfigs.length) =
      UInt256.ofNat c.assetConfigs.length := by
    rw [u256_land_comm]
    apply u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide)
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
    change c.assetConfigs.length < 2^8
    omega
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  have hrate (j : Nat) : UInt256.div (constructorRecordWord c j) (UInt256.ofNat 31536000) =
      constructorRateWord c j := rfl
  have hr12 : UInt256.land (constructorRateWord c 12) constructorMask64 =
      constructorRateWord c 12 := by
    rw [u256_land_comm, constructorRateWord_clean c (by decide) (by decide)]
  unfold constructorBorrowMemory at hdelegate hptr
  unfold cometWithExtendedAssetListCreation_block_1200_stack
    cometWithExtendedAssetListCreation_block_1200_memory
  simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hwrite, hr1, hr2, hr3, hr4, hr5,
    constructorRecordWord_clean64, hrate, constructorRateWord_clean, hr12, hnclean, hdelegate, hptr]
  exact ⟨trivial, rfl⟩

end Benchmarks.CompoundIII.Comet
