import Benchmarks.CompoundIII.Comet.ConstructorDecimalsCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem constructorDecimalsAllocation_fits {c : ConstructorConfig}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64) :
    constructorAssetFree c c.assetConfigs.length + 32 < 2^64 := by
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase at *
  omega

theorem constructorDecimalsMemory_size (c : ConstructorConfig) :
    (constructorDecimalsMemory c).size = constructorAssetFree c c.assetConfigs.length + 32 := by
  rw [constructorDecimalsMemory, writeWord_sparse_size, constructorDecodedMemory_size]
  omega

theorem constructorDecimalsCopyMemory_size {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hhi : out.size < UInt256.size) :
    (constructorDecimalsCopyMemory c out).size =
      constructorAssetFree c c.assetConfigs.length + 32 := by
  rw [constructorDecimalsCopyMemory, callOutput32_size _ _ _ hhi (by
    rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega), constructorDecimalsMemory_size]),
    constructorDecimalsMemory_size]

def constructorDecimalsReturnMemory (c : ConstructorConfig) (out : ByteArray) : ByteArray :=
  writeWord (constructorDecimalsCopyMemory c out) 64
    (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 32))

theorem constructorDecimalsReturnMemory_word {c : ConstructorConfig} {out : ByteArray}
    (hfree : constructorAssetFree c c.assetConfigs.length < 2^64)
    (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size) :
    memLoad (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length))
      (constructorDecimalsReturnMemory c out) = calldataWord out 0 := by
  have hp : (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toNat =
      constructorAssetFree c c.assetConfigs.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hlow : 96 ≤ constructorAssetFree c c.assetConfigs.length := by
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    omega
  apply loadedWord_of_read
  · rw [hp, constructorDecimalsReturnMemory, writeWord_sparse_size,
      constructorDecimalsCopyMemory_size hfree hhi]
    omega
  · rw [constructorDecimalsReturnMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by rw [hp]; exact hlow, by
        rw [hp, constructorDecimalsCopyMemory_size hfree hhi]⟩)]
    exact callOutput32_read_word _ _ _ hhi hlo (by rw [hp, constructorDecimalsMemory_size]; omega)

end Benchmarks.CompoundIII.Comet
