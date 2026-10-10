import Benchmarks.CompoundIII.Comet.ConstructorFactoryResponse

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorFactoryPtr (c : ConstructorConfig) : UInt256 :=
  UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 64)

theorem constructorFactoryPtr_toNat {c : ConstructorConfig} (hn : c.assetConfigs.length ≤ 24) :
    (constructorFactoryPtr c).toNat = constructorAssetFree c c.assetConfigs.length + 64 := by
  apply UInt256.toNat_ofNat_of_lt
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
  change _ < 2^256
  omega

theorem constructorFactoryPtr_fits {c : ConstructorConfig} (hn : c.assetConfigs.length ≤ 24) :
    (constructorFactoryPtr c).toNat + 32 < 2^64 := by
  rw [constructorFactoryPtr_toNat hn]
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
  omega

theorem constructorFactoryPtr_ge {c : ConstructorConfig} (hn : c.assetConfigs.length ≤ 24) :
    96 ≤ (constructorFactoryPtr c).toNat := by
  rw [constructorFactoryPtr_toNat hn]
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
  omega

def constructorFactoryBaseMemory (c : ConstructorConfig) (w : UInt256)
    (out feed : ByteArray) : ByteArray :=
  constructorRemainingImmMemory c w (constructorScaleMemory c w
    (constructorInitialImmMemory c w (constructorPriceFeedReturnMemory c out feed)))

def constructorFactoryInputMemory (c : ConstructorConfig) (w : UInt256)
    (out feed : ByteArray) : ByteArray :=
  writeWord (constructorFactoryBaseMemory c w out feed) (constructorFactoryPtr c).toNat
    constructorFactorySelectorWord

theorem constructorFactoryBaseMemory_size {c : ConstructorConfig} {w : UInt256}
    {out feed : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) :
    (constructorFactoryBaseMemory c w out feed).size = (constructorFactoryPtr c).toNat := by
  have hfree : constructorAssetFree c c.assetConfigs.length < 2^64 := by
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    omega
  have hs : (constructorPriceFeedReturnMemory c out feed).size =
      constructorAssetFree c c.assetConfigs.length + 64 := by
    rw [constructorPriceFeedReturnMemory, writeWord_sparse_size, constructorPriceFeedCopyMemory,
      callOutput32_size _ _ _ hfeed (by rw [constructorPriceFeedMemory_size hfree hout]),
      constructorPriceFeedMemory_size hfree hout, constructorPriceFeedPtr_toNat hfree]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    omega
  unfold constructorFactoryBaseMemory constructorRemainingImmMemory constructorBorrowMemory
    constructorSupplyMemory constructorRewardMemory constructorScaleMemory
    constructorInitialImmMemory
  simp only [writeWord_sparse_size, hs, constructorFactoryPtr_toNat hn]
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
  omega

theorem constructorFactoryInputMemory_size {c : ConstructorConfig} {w : UInt256}
    {out feed : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) :
    (constructorFactoryInputMemory c w out feed).size = (constructorFactoryPtr c).toNat + 32 := by
  rw [constructorFactoryInputMemory, writeWord_sparse_size,
    constructorFactoryBaseMemory_size hn hout hfeed]
  omega

theorem constructorFactoryInputMemory_payload {c : ConstructorConfig} {w : UInt256}
    {out feed : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) :
    (constructorFactoryInputMemory c w out feed).readWithPadding (constructorFactoryPtr c).toNat 4 =
      constructorFactoryPayload := by
  have hr := toByteArray_write_read_window_of_gap constructorFactorySelectorWord
    (constructorFactoryBaseMemory c w out feed) (constructorFactoryPtr c).toNat 0 4
    (by decide) (by decide) (by decide) (by
      rw [constructorFactoryBaseMemory_size hn hout hfeed, Nat.sub_self]
      exact lt_usize 0 (by decide))
  have hsel : constructorFactorySelectorWord.toByteArray.extract 0 (0 + 4) =
      constructorFactoryPayload := by decide +kernel
  simpa only [Nat.add_zero] using hr.trans hsel

end Benchmarks.CompoundIII.Comet
