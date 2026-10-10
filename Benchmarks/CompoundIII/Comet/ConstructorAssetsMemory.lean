import Benchmarks.CompoundIII.Comet.CreateAssetListResponse
import Benchmarks.CompoundIII.Comet.ConstructorFactoryMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorAssetsPtr (c : ConstructorConfig) : Nat :=
  constructorAssetFree c c.assetConfigs.length + 96

theorem constructorAssetsPtr_fits {c : ConstructorConfig} (hn : c.assetConfigs.length ≤ 24) :
    constructorAssetsPtr c + 68 + 224 * c.assetConfigs.length < 2^64 := by
  unfold constructorAssetsPtr constructorAssetFree constructorArrayEnd constructorArrayBase
    constructorRecordBase
  omega

theorem constructorAssetsPtr_toNat {c : ConstructorConfig} (hn : c.assetConfigs.length ≤ 24) :
    (UInt256.ofNat (constructorAssetsPtr c)).toNat = constructorAssetsPtr c := by
  have h := constructorAssetsPtr_fits hn
  exact UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)

def constructorAssetsBaseMemory (c : ConstructorConfig) (w : UInt256)
    (out feed factoryOut : ByteArray) : ByteArray :=
  constructorFactoryReturnMemory (constructorFactoryInputMemory c w out feed)
    factoryOut (constructorFactoryPtr c)

def constructorAssetsInputMemory (c : ConstructorConfig) (w : UInt256)
    (out feed factoryOut : ByteArray) : ByteArray :=
  createAssetListEvmMemory c (constructorAssetsBaseMemory c w out feed factoryOut)
    (constructorAssetsPtr c) c.assetConfigs.length

theorem ConstructorDataMemory.preserved {c : ConstructorConfig} {before after : ByteArray}
    (hm : ConstructorDataMemory c before)
    (hp : MemoryPrefix before after (constructorAssetFree c c.assetConfigs.length)) :
    ConstructorDataMemory c after := by
  refine ⟨le_trans hm.present hp.size, ?_⟩
  intro ptr hlo hhi
  rw [memoryPrefix_load hp (by unfold constructorRecordBase at hlo; omega) hhi
    (le_trans hhi hm.present)]
  exact hm.words ptr hlo hhi

theorem constructorAssetsBaseMemory_data {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size)
    (hfactory : factoryOut.size < UInt256.size) :
    ConstructorDataMemory c (constructorAssetsBaseMemory c w out feed factoryOut) := by
  have hfree : constructorAssetFree c c.assetConfigs.length < 2^64 := by
    have h := constructorAssetsPtr_fits hn
    unfold constructorAssetsPtr at h
    omega
  have hbase : ConstructorDataMemory c (constructorFactoryBaseMemory c w out feed) :=
    constructorBorrowMemory_data (constructorSupplyMemory_data
      (constructorRewardMemory_data (constructorScaleMemory_data
        (constructorInitialImmMemory_data
          (ConstructorDataMemory.priceFeed hfree hout hfeed) w) w) w))
  have hin : ConstructorDataMemory c (constructorFactoryInputMemory c w out feed) :=
    hbase.writeAbove _ (by rw [constructorFactoryPtr_toNat hn]; omega)
  have hp : MemoryPrefix (constructorFactoryInputMemory c w out feed)
      (callOutputMem (constructorFactoryInputMemory c w out feed) factoryOut
        (constructorFactoryPtr c) ⟨32⟩) (constructorAssetFree c c.assetConfigs.length) :=
    (callOutput32_prefix (constructorFactoryInputMemory c w out feed) factoryOut
    (constructorFactoryPtr c) hfactory
    (by rw [constructorFactoryInputMemory_size hn hout hfeed])).mono
      (by rw [constructorFactoryPtr_toNat hn]; omega)
  exact (hin.preserved hp).writeBelow _ (by unfold constructorRecordBase; omega)

theorem constructorAssetsBaseMemory_free {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut : ByteArray} (hn : c.assetConfigs.length ≤ 24) :
    memLoad (UInt256.ofNat 64) (constructorAssetsBaseMemory c w out feed factoryOut) =
      UInt256.ofNat (constructorAssetsPtr c) := by
  have hr : memLoad (UInt256.ofNat 64) (constructorAssetsBaseMemory c w out feed factoryOut) =
      constructorFactoryPtr c + UInt256.ofNat 32 := memLoad_writeWord_self _ (UInt256.ofNat 64) _
  rw [hr]
  rw [constructorFactoryPtr, u256_ofNat_add_eq (by
    have h := constructorAssetsPtr_fits hn
    unfold constructorAssetsPtr at h
    change _ < 2^256
    omega)]
  rfl

theorem constructorAssetsInputMemory_size {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut : ByteArray} (hn : c.assetConfigs.length ≤ 24) :
    constructorAssetsPtr c + 68 + 224 * c.assetConfigs.length ≤
      (constructorAssetsInputMemory c w out feed factoryOut).size := by
  unfold constructorAssetsInputMemory
  rw [createAssetListEvmMemory_size (Nat.le_refl _) (by
    have h := constructorAssetsPtr_fits hn; omega)]
  exact Nat.le_max_right _ _

end Benchmarks.CompoundIII.Comet
