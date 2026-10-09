import Benchmarks.CompoundIII.Comet.ConstructorRuntimeWindow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorRuntimeSites : List (Nat × Nat) :=
  immutableReferences.zipIdx.flatMap fun ((_, sites), i) ↦
    sites.map fun off ↦ (off, 128 + 32 * i)

def constructorRuntimeWords (w : Nat → UInt256) : String → UInt256
  | "governor" => w 128
  | "pauseGuardian" => w 160
  | "baseToken" => w 192
  | "baseTokenPriceFeed" => w 224
  | "extensionDelegate" => w 256
  | "supplyKink" => w 288
  | "supplyPerSecondInterestRateSlopeLow" => w 320
  | "supplyPerSecondInterestRateSlopeHigh" => w 352
  | "supplyPerSecondInterestRateBase" => w 384
  | "borrowKink" => w 416
  | "borrowPerSecondInterestRateSlopeLow" => w 448
  | "borrowPerSecondInterestRateSlopeHigh" => w 480
  | "borrowPerSecondInterestRateBase" => w 512
  | "storeFrontPriceFactor" => w 544
  | "baseScale" => w 576
  | "trackingIndexScale" => w 608
  | "baseTrackingSupplySpeed" => w 640
  | "baseTrackingBorrowSpeed" => w 672
  | "baseMinForRewards" => w 704
  | "baseBorrowMin" => w 736
  | "targetReserves" => w 768
  | "decimals" => w 800
  | "numAssets" => w 832
  | "accrualDescaleFactor" => w 864
  | "assetList" => w 896
  | _ => ⟨0⟩

theorem constructorRuntimeSites_length : constructorRuntimeSites.length = 70 := by decide

theorem constructorRuntimeSites_bounded :
    ∀ p ∈ constructorRuntimeSites, p.1 + 32 ≤ 18599 := by decide

theorem constructorRuntimeSites_layout (w : Nat → UInt256) :
    constructorRuntimeSites.map (fun (off, slot) ↦ (off, w slot)) =
      immutableLayout.writes (constructorRuntimeWords w) := rfl

def constructorRuntimeCopy (mem tail : ByteArray) (ptr : UInt256) : ByteArray :=
  (cometWithExtendedAssetListCreationBytecode ++ tail).write 2826 mem ptr.toNat 18599

def constructorRuntimePatchedMemory (mem : ByteArray) (ptr : UInt256) (w : Nat → UInt256)
    (n : Nat) : ByteArray :=
  writeCascade mem ((constructorRuntimeSites.take n).map fun (off, slot) ↦
    (ptr.toNat + off, w slot))

theorem constructorRuntimeCopy_prefix {mem tail : ByteArray} {ptr : UInt256}
    (hp : ptr.toNat ≤ mem.size) :
    MemoryPrefix mem (constructorRuntimeCopy mem tail ptr) ptr.toNat := by
  exact copyWindow_prefix _ _ _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, cometCreationBytecode_size]; omega) hp (Or.inl (le_refl _))

theorem constructorRuntimeCopy_size {mem tail : ByteArray} {ptr : UInt256}
    (hp : ptr.toNat ≤ mem.size) :
    (constructorRuntimeCopy mem tail ptr).size = max mem.size (ptr.toNat + 18599) := by
  exact copyWindow_size _ _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, cometCreationBytecode_size]; omega) hp

theorem constructorRuntimeCopy_template {mem tail : ByteArray} {ptr : UInt256}
    (hp : ptr.toNat ≤ mem.size) :
    (constructorRuntimeCopy mem tail ptr).extract ptr.toNat (ptr.toNat + 18599) =
      cometWithExtendedAssetListBytecode := by
  have hc : cometWithExtendedAssetListCreationBytecode.extract 2826 (2826 + 18599) =
      cometWithExtendedAssetListBytecode := by native_decide
  have hr := copyWindow_extract (cometWithExtendedAssetListCreationBytecode ++ tail) mem
    2826 ptr.toNat 18599 0 18599 (by decide)
    (by rw [ByteArray.size_append, cometCreationBytecode_size]; omega) hp (by decide)
  simp only [Nat.add_zero] at hr
  exact hr.trans ((byteArray_extract_append_left cometWithExtendedAssetListCreationBytecode
    tail 2826 (2826 + 18599)
    (by rw [cometCreationBytecode_size])).trans hc)

theorem constructorRuntimePatchedMemory_prefix (mem : ByteArray) (ptr : UInt256)
    (w : Nat → UInt256) (n : Nat) :
    MemoryPrefix mem (constructorRuntimePatchedMemory mem ptr w n) ptr.toNat := by
  apply memoryPrefix_sparse_cascade
  intro p hp
  obtain ⟨⟨off, slot⟩, _, rfl⟩ := List.mem_map.mp hp
  exact Or.inl (Nat.le_add_right _ _)

theorem constructorRuntimePatchedMemory_low {mem : ByteArray} {ptr read : UInt256}
    {w : Nat → UInt256} {n : Nat} (hlo : 96 ≤ read.toNat)
    (hhi : read.toNat + 32 ≤ ptr.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (constructorRuntimePatchedMemory mem ptr w n) = memLoad read mem :=
  memoryPrefix_load (constructorRuntimePatchedMemory_prefix _ _ _ _) hlo hhi hin

theorem constructorRuntimePatchedMemory_return {mem tail : ByteArray} {ptr : UInt256}
    {w : Nat → UInt256} (hp : ptr.toNat ≤ mem.size) :
    (constructorRuntimePatchedMemory (constructorRuntimeCopy mem tail ptr) ptr w 70).readWithPadding
      ptr.toNat 18599 = immutableLayout.runtime cometWithExtendedAssetListBytecode
        (constructorRuntimeWords w) := by
  have hin : ptr.toNat + 18599 ≤ (constructorRuntimeCopy mem tail ptr).size := by
    rw [constructorRuntimeCopy_size hp]
    exact Nat.le_max_right _ _
  have hs := (constructorRuntimePatchedMemory_prefix (constructorRuntimeCopy mem tail ptr)
    ptr w 70).size
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (le_trans hin hs)]
  unfold constructorRuntimePatchedMemory
  rw [List.take_of_length_le (by rw [constructorRuntimeSites_length])]
  have he := writeCascade_extract_window (constructorRuntimeCopy mem tail ptr) ptr.toNat 18599
    (constructorRuntimeSites.map fun (off, slot) ↦ (off, w slot)) hin (by
      intro p hp
      obtain ⟨⟨off, slot⟩, hsite, rfl⟩ := List.mem_map.mp hp
      exact constructorRuntimeSites_bounded (off, slot) hsite)
  simp only [List.map_map, Function.comp_def] at he
  apply he.trans
  rw [constructorRuntimeCopy_template hp, constructorRuntimeSites_layout]
  rfl

end Benchmarks.CompoundIII.Comet
