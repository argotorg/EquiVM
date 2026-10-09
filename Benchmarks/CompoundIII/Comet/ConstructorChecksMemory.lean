import Benchmarks.CompoundIII.Comet.ConstructorDecimalsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorDecimalsReturnMemory_prefix {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    MemoryPrefix (constructorDecodedMemory c) (constructorDecimalsReturnMemory c out)
      (constructorAssetFree c c.assetConfigs.length) := by
  have hp : (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat =
      constructorAssetFree c c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hi := memoryPrefix_sparse_writeWord (constructorDecodedMemory c)
    (constructorAssetFree c c.assetConfigs.length)
    (constructorAssetFree c c.assetConfigs.length)
    (UInt256.shiftLeft (UInt256.ofNat 826074471) (UInt256.ofNat 224)) (Or.inl (le_refl _))
  have hc := callOutput32_prefix (constructorDecimalsMemory c) out
    (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)) hout
    (by rw [hp, constructorDecimalsMemory_size])
  rw [hp] at hc
  exact (hi.trans hc).trans
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))

theorem constructorDecimalsReturnMemory_load {c : ConstructorConfig} {out : ByteArray}
    {ptr : UInt256} (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) (hlo : 96 ≤ ptr.toNat)
    (hlim : ptr.toNat + 32 ≤ constructorAssetFree c c.assetConfigs.length) :
    memLoad ptr (constructorDecimalsReturnMemory c out) =
      memLoad ptr (constructorDecodedMemory c) :=
  memoryPrefix_load (constructorDecimalsReturnMemory_prefix hfree hout) hlo hlim
    (by rw [constructorDecodedMemory_size]; exact hlim)

theorem constructorDecimalsReturnMemory_scalar {c : ConstructorConfig} {out : ByteArray}
    {j : Nat} (hj : j < 20) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat (32 * j))
      (constructorDecimalsReturnMemory c out) = constructorRecordWord c j := by
  rw [constructorDecimalsReturnMemory_load hfree hout]
  · exact constructorDecodedMemory_scalar hj hsize
  · rw [constructorRecordBase_add_toNat (by omega) hsize]
    unfold constructorRecordBase
    omega
  · rw [constructorRecordBase_add_toNat (by omega) hsize]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    omega

theorem constructorDecimalsReturnMemory_assets {c : ConstructorConfig} {out : ByteArray}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 640)
      (constructorDecimalsReturnMemory c out) = UInt256.ofNat (constructorArrayBase c) := by
  rw [constructorDecimalsReturnMemory_load hfree hout]
  · exact constructorDecodedMemory_assets hsize
  · rw [constructorRecordBase_add_toNat (by decide) hsize]
    unfold constructorRecordBase
    omega
  · rw [constructorRecordBase_add_toNat (by decide) hsize]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase
    omega

theorem constructorDecodedMemory_assetCount {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorArrayBase c)) (constructorDecodedMemory c) =
      UInt256.ofNat c.assetConfigs.length := by
  have hb : (UInt256.ofNat (constructorArrayBase c)).toNat = constructorArrayBase c := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorArrayBase constructorRecordBase
    omega
  have hp := constructorAssetLoopMemory_headerPrefix c c.assetConfigs.length
  have hs := hp.size
  rw [constructorArrayHeaderMemory_size] at hs
  apply loadedWord_of_read
  · rw [hb, constructorDecodedMemory_size]
    unfold constructorAssetFree constructorArrayEnd
    omega
  · rw [hb, constructorDecodedMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by unfold constructorArrayBase; omega, hs⟩),
      hp.read _ (by unfold constructorArrayBase constructorRecordBase; omega) (le_refl _)
        (by rw [constructorArrayHeaderMemory_size])]
    exact writeWord_sparse_read_back _ _ _

theorem constructorDecimalsReturnMemory_assetCount {c : ConstructorConfig} {out : ByteArray}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat (constructorArrayBase c)) (constructorDecimalsReturnMemory c out) =
      UInt256.ofNat c.assetConfigs.length := by
  have hb : (UInt256.ofNat (constructorArrayBase c)).toNat = constructorArrayBase c := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorArrayBase constructorRecordBase
    omega
  rw [constructorDecimalsReturnMemory_load hfree hout]
  · exact constructorDecodedMemory_assetCount hsize
  · rw [hb]
    unfold constructorArrayBase constructorRecordBase
    omega
  · rw [hb]
    unfold constructorAssetFree constructorArrayEnd
    omega

theorem constructorDecimalsReturnMemory_free (c : ConstructorConfig) (out : ByteArray) :
    memLoad (UInt256.ofNat 64) (constructorDecimalsReturnMemory c out) =
      UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 32) := by
  apply loadedWord_of_read
  · change 64 + 32 ≤ _
    rw [constructorDecimalsReturnMemory, writeWord_sparse_size]
    omega
  · exact writeWord_sparse_read_back _ _ _

end Benchmarks.CompoundIII.Comet
