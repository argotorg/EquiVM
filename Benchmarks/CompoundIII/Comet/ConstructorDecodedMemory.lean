import Benchmarks.CompoundIII.Comet.ConstructorAssetLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: read back any earlier word from a consecutive word-store sequence.
theorem constructorConsecutiveWords_read {memory : Nat → ByteArray} {word : Nat → UInt256}
    {base : Nat}
    (hwrite : ∀ n, memory (n + 1) = writeWord (memory n) (base + 32 * n) (word n))
    (hsize : ∀ n, 0 < n → base + 32 * n ≤ (memory n).size) {j n : Nat} (hj : j < n) :
    (memory n).readWithPadding (base + 32 * j) 32 = (word j).toByteArray := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [hwrite]
    by_cases he : j = n
    · subst j
      exact writeWord_sparse_read_back _ _ _
    · rw [writeWord_sparse_read_preserved _ _ _ _
        (Or.inl ⟨by omega, by have hs := hsize n (by omega); omega⟩)]
      exact ih (by omega)

theorem constructorScalarMemory_readStored {c : ConstructorConfig} {j n : Nat} (hj : j < n) :
    (constructorScalarMemory c n).readWithPadding (constructorRecordBase c + 32 * j) 32 =
      (constructorRecordWord c j).toByteArray := by
  exact constructorConsecutiveWords_read (fun _ ↦ rfl)
    (fun n _ ↦ by rw [constructorScalarMemory_size]) hj

theorem constructorAssetFieldMemory_readStored {mem : ByteArray} {dst : Nat}
    {a : ConstructorAsset} {j n : Nat} (hj : j < n) :
    (constructorAssetFieldMemory mem dst a n).readWithPadding (dst + 32 * j) 32 =
      (a.word j).toByteArray := by
  exact constructorConsecutiveWords_read (fun _ ↦ rfl)
    (fun n hn ↦ by rw [constructorAssetFieldMemory_size _ _ _ hn]; omega) hj

theorem constructorAssetLoopMemory_headerPrefix (c : ConstructorConfig) (i : Nat) :
    MemoryPrefix (constructorArrayHeaderMemory c) (constructorAssetLoopMemory c i)
      (constructorArrayBase c + 32) := by
  induction i with
  | zero => exact .refl _ _
  | succ i ih =>
    rw [constructorAssetLoopMemory]
    split
    · exact ih.trans (constructorAssetStoreMemory_prefix _ _ _ _
        (by unfold constructorAssetFree constructorArrayEnd; omega)
        (by unfold constructorAssetEntry; omega))
    · exact ih

theorem constructorAssetLoopMemory_scalarPrefix (c : ConstructorConfig) (i : Nat) :
    MemoryPrefix (constructorScalarMemory c 20) (constructorAssetLoopMemory c i)
      (constructorArrayBase c) := by
  apply (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
  apply (memoryPrefix_sparse_writeWord _ (constructorArrayBase c) _ _ (Or.inl (by omega))).trans
  exact (constructorAssetLoopMemory_headerPrefix c i).mono (by omega)

def constructorDecodedMemory (c : ConstructorConfig) : ByteArray :=
  writeWord (constructorAssetLoopMemory c c.assetConfigs.length) (constructorRecordBase c + 640)
    (UInt256.ofNat (constructorArrayBase c))

theorem constructorDecodedMemory_scalarPrefix (c : ConstructorConfig) :
    MemoryPrefix (constructorScalarMemory c 20) (constructorDecodedMemory c)
      (constructorRecordBase c + 640) := by
  apply ((constructorAssetLoopMemory_scalarPrefix c _).mono
    (by unfold constructorArrayBase; omega)).trans
  exact memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))

theorem constructorDecodedMemory_scalar {c : ConstructorConfig} {j : Nat} (hj : j < 20)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat (32 * j))
      (constructorDecodedMemory c) = constructorRecordWord c j := by
  have hoff := constructorRecordBase_add_toNat (c := c) (off := 32 * j) (by omega) hsize
  have hp := constructorDecodedMemory_scalarPrefix c
  apply mloadWordValue_of_readWithPadding
  · have hs := hp.size
    rw [constructorScalarMemory_size] at hs
    rw [hoff]
    omega
  · rw [hoff, hp.read _ (by unfold constructorRecordBase; omega) (by omega)
      (by rw [constructorScalarMemory_size]; omega)]
    exact constructorScalarMemory_readStored hj

theorem constructorDecodedMemory_readFree (c : ConstructorConfig) :
    (constructorDecodedMemory c).readWithPadding 64 32 =
      (UInt256.ofNat (constructorAssetFree c c.assetConfigs.length)).toByteArray := by
  rw [constructorDecodedMemory, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨by unfold constructorRecordBase; omega, by
      have hs := (constructorAssetLoopMemory_headerPrefix c c.assetConfigs.length).size
      rw [constructorArrayHeaderMemory_size] at hs
      unfold constructorArrayBase constructorRecordBase at hs
      omega⟩)]
  exact constructorAssetLoopMemory_readFree (Nat.le_refl _)

theorem constructorDecodedMemory_free (c : ConstructorConfig) :
    memLoad (UInt256.ofNat 64) (constructorDecodedMemory c) =
      UInt256.ofNat (constructorAssetFree c c.assetConfigs.length) := by
  apply mloadWordValue_of_readWithPadding
  · have hs := (constructorDecodedMemory_scalarPrefix c).size
    rw [constructorScalarMemory_size] at hs
    change 64 < _
    unfold constructorRecordBase at hs
    omega
  · exact constructorDecodedMemory_readFree c

theorem constructorDecodedMemory_assets {c : ConstructorConfig}
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (constructorRecordBase c) + UInt256.ofNat 640)
      (constructorDecodedMemory c) = UInt256.ofNat (constructorArrayBase c) := by
  apply mloadWordValue_of_readWithPadding
  · rw [constructorRecordBase_add_toNat (by decide) hsize,
      constructorDecodedMemory, writeWord_sparse_size]
    omega
  · rw [constructorRecordBase_add_toNat (by decide) hsize]
    exact writeWord_sparse_read_back _ _ _

end Benchmarks.CompoundIII.Comet
