import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedMemory
import Benchmarks.CompoundIII.Comet.MemoryLoadPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

/-- The decoded configuration and asset records survive writes to the constructor's immutable
    slots and to subsequent external-call buffers. -/
structure ConstructorDataMemory (c : ConstructorConfig) (mem : ByteArray) : Prop where
  present : constructorAssetFree c c.assetConfigs.length ≤ mem.size
  words : ∀ ptr : UInt256, constructorRecordBase c ≤ ptr.toNat →
    ptr.toNat + 32 ≤ constructorAssetFree c c.assetConfigs.length →
    memLoad ptr mem = memLoad ptr (constructorDecodedMemory c)

theorem constructorPriceFeedReturnMemory_prefix {c : ConstructorConfig} {out feed : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) :
    MemoryPrefix (constructorDecodedMemory c) (constructorPriceFeedReturnMemory c out feed)
      (constructorAssetFree c c.assetConfigs.length) := by
  have hi := memoryPrefix_sparse_writeWord (constructorDecimalsReturnMemory c out)
    (constructorPriceFeedPtr c).toNat (constructorPriceFeedPtr c).toNat
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224)) (Or.inl (le_refl _))
  have hc := callOutput32_prefix (constructorPriceFeedMemory c out) feed
    (constructorPriceFeedPtr c) hfeed (by rw [constructorPriceFeedMemory_size hfree hout])
  have hp := (hi.trans hc).trans
    (memoryPrefix_sparse_writeWord _ 64 _
      (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 64)) (Or.inr (by decide)))
  exact (constructorDecimalsReturnMemory_prefix hfree hout).trans
    (hp.mono (by rw [constructorPriceFeedPtr_toNat hfree]; omega))

theorem ConstructorDataMemory.priceFeed {c : ConstructorConfig} {out feed : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size) :
    ConstructorDataMemory c (constructorPriceFeedReturnMemory c out feed) := by
  have hp := constructorPriceFeedReturnMemory_prefix hfree hout hfeed
  refine ⟨?_, ?_⟩
  · simpa only [constructorDecodedMemory_size] using hp.size
  · intro ptr hlo hhi
    exact memoryPrefix_load hp (by unfold constructorRecordBase at hlo; omega) hhi
      (by rw [constructorDecodedMemory_size]; exact hhi)

theorem ConstructorDataMemory.writeBelow {c : ConstructorConfig} {mem : ByteArray} {off : Nat}
    (hm : ConstructorDataMemory c mem) (word : UInt256)
    (hoff : off + 32 ≤ constructorRecordBase c) :
    ConstructorDataMemory c (writeWord mem off word) := by
  refine ⟨?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans hm.present (Nat.le_max_left _ _)
  · intro ptr hlo hhi
    rw [memLoad_writeWord_preserved _ _ _ _ (le_trans hhi hm.present) (Or.inr (by omega))]
    exact hm.words ptr hlo hhi

theorem ConstructorDataMemory.scalar {c : ConstructorConfig} {mem : ByteArray} {j : Nat}
    (hm : ConstructorDataMemory c mem) (hj : j < 20)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat (32 * j)) mem =
      constructorRecordWord c j := by
  rw [hm.words _ (by rw [constructorRecordBase_add_toNat (by omega) hsize]; omega) (by
    rw [constructorRecordBase_add_toNat (by omega) hsize]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    omega)]
  exact constructorDecodedMemory_scalar hj hsize

theorem ConstructorDataMemory.assets {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 640) mem =
      UInt256.ofNat (constructorArrayBase c) := by
  rw [hm.words _ (by rw [constructorRecordBase_add_toNat (by decide) hsize]; omega) (by
    rw [constructorRecordBase_add_toNat (by decide) hsize]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    omega)]
  exact constructorDecodedMemory_assets hsize

theorem ConstructorDataMemory.assetCount {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorArrayBase c)) mem = UInt256.ofNat c.assetConfigs.length := by
  have hb : (UInt256.ofNat (constructorArrayBase c)).toNat = constructorArrayBase c := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorArrayBase constructorRecordBase
    omega
  rw [hm.words _ (by rw [hb]; unfold constructorArrayBase; omega) (by
    rw [hb]
    unfold constructorAssetFree constructorArrayEnd
    omega)]
  exact constructorDecodedMemory_assetCount hsize

end Benchmarks.CompoundIII.Comet
