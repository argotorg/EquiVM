import Benchmarks.CompoundIII.Comet.ConstructorChecksMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorPriceFeedPtr (c : ConstructorConfig) : UInt256 :=
  UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 32)

def constructorPriceFeedMemory (c : ConstructorConfig) (out : ByteArray) : ByteArray :=
  writeWord (constructorDecimalsReturnMemory c out) (constructorPriceFeedPtr c).toNat
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224))

def constructorPriceFeedCopyMemory (c : ConstructorConfig) (out feed : ByteArray) : ByteArray :=
  callOutputMem (constructorPriceFeedMemory c out) feed (constructorPriceFeedPtr c) ⟨32⟩

def constructorPriceFeedReturnMemory (c : ConstructorConfig) (out feed : ByteArray) : ByteArray :=
  writeWord (constructorPriceFeedCopyMemory c out feed) 64
    (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 64))

theorem constructorPriceFeedPtr_toNat {c : ConstructorConfig}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64) :
    (constructorPriceFeedPtr c).toNat = constructorAssetFree c c.assetConfigs.length + 32 := by
  apply UInt256.toNat_ofNat_of_lt
  have hh := constructorDecimalsAllocation_fits hfree
  change _ < 2^256
  omega

theorem constructorPriceFeedPtr_fits {c : ConstructorConfig}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64) :
    (constructorPriceFeedPtr c).toNat + 32 < 2^64 := by
  rw [constructorPriceFeedPtr_toNat hfree]
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase at *
  omega

theorem constructorDecimalsReturnMemory_size {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    (constructorDecimalsReturnMemory c out).size =
      constructorAssetFree c c.assetConfigs.length + 32 := by
  rw [constructorDecimalsReturnMemory, writeWord_sparse_size,
    constructorDecimalsCopyMemory_size hfree hout]
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
  omega

theorem constructorPriceFeedMemory_size {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    (constructorPriceFeedMemory c out).size = (constructorPriceFeedPtr c).toNat + 32 := by
  rw [constructorPriceFeedMemory, writeWord_sparse_size,
    constructorDecimalsReturnMemory_size hfree hout, constructorPriceFeedPtr_toNat hfree]
  omega

theorem constructorPriceFeedMemory_payload {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    (constructorPriceFeedMemory c out).readWithPadding (constructorPriceFeedPtr c).toNat 4 =
      decimalsPayload := by
  have hr := toByteArray_write_read_window_of_gap
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224))
    (constructorDecimalsReturnMemory c out) (constructorPriceFeedPtr c).toNat 0 4
    (by decide) (by decide) (by decide) (by
      rw [constructorDecimalsReturnMemory_size hfree hout, constructorPriceFeedPtr_toNat hfree,
        Nat.sub_self]
      exact lt_usize 0 (by decide))
  have hsel : (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224)).toByteArray.extract
      0 (0 + 4) = decimalsPayload := by decide +kernel
  simpa only [Nat.add_zero] using hr.trans hsel

theorem constructorPriceFeedReturnMemory_word {c : ConstructorConfig} {out feed : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) (hlo : 32 ≤ feed.size) :
    memLoad (constructorPriceFeedPtr c) (constructorPriceFeedReturnMemory c out feed) =
      calldataWord feed 0 := by
  have hs : (constructorPriceFeedCopyMemory c out feed).size =
      (constructorPriceFeedPtr c).toNat + 32 := by
    rw [constructorPriceFeedCopyMemory, callOutput32_size _ _ _ hfeed
      (by rw [constructorPriceFeedMemory_size hfree hout]),
      constructorPriceFeedMemory_size hfree hout]
  apply loadedWord_of_read
  · rw [constructorPriceFeedReturnMemory, writeWord_sparse_size, hs]
    omega
  · rw [constructorPriceFeedReturnMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by
        rw [constructorPriceFeedPtr_toNat hfree]
        unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
        omega, by rw [hs]⟩)]
    exact callOutput32_read_word _ _ _ hfeed hlo
      (by rw [constructorPriceFeedMemory_size hfree hout]; omega)

end Benchmarks.CompoundIII.Comet
