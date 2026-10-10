import Benchmarks.CompoundIII.Comet.ConstructorDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem ConstructorDataMemory.writeAbove {c : ConstructorConfig} {mem : ByteArray} {off : Nat}
    (hm : ConstructorDataMemory c mem) (word : UInt256)
    (hoff : constructorAssetFree c c.assetConfigs.length ≤ off) :
    ConstructorDataMemory c (writeWord mem off word) := by
  refine ⟨?_, ?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans hm.present (Nat.le_max_left _ _)
  · intro ptr hlo hhi
    rw [memLoad_writeWord_preserved _ _ _ _ (le_trans hhi hm.present) (Or.inl (by omega))]
    exact hm.words ptr hlo hhi

theorem constructorAssetLoopMemory_readEntry {c : ConstructorConfig} {i n : Nat}
    (hi : i < n) (hn : n ≤ c.assetConfigs.length) :
    (constructorAssetLoopMemory c n).readWithPadding (constructorAssetEntry c i) 32 =
      (UInt256.ofNat (constructorAssetFree c i)).toByteArray := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [constructorAssetLoopMemory, dif_pos (by omega)]
    by_cases he : i = n
    · subst i
      exact writeWord_sparse_read_back _ _ _
    · have hp := constructorAssetStoreMemory_prefix (constructorAssetLoopMemory c n)
        (constructorAssetFree c n) (constructorAssetEntry c n) c.assetConfigs[n]
        (limit := constructorAssetEntry c n)
        (by unfold constructorAssetFree constructorAssetEntry constructorArrayEnd; omega)
        (le_refl _)
      apply Eq.trans (hp.read (constructorAssetEntry c i) (by
        unfold constructorAssetEntry constructorArrayBase constructorRecordBase; omega) (by
        unfold constructorAssetEntry; omega) (by
        rw [constructorAssetLoopMemory_size (by omega), if_neg (by omega)]
        unfold constructorAssetEntry constructorAssetFree constructorArrayEnd
        omega))
      exact ih (by omega) (by omega)

theorem constructorAssetStoreMemory_readEarlier {mem : ByteArray} {dst entry off : Nat}
    {a : ConstructorAsset} (hlo : 96 ≤ off) (hhi : off + 32 ≤ dst)
    (he : entry + 32 ≤ off) (hm : off + 32 ≤ mem.size) :
    (constructorAssetStoreMemory mem dst entry a).readWithPadding off 32 =
      mem.readWithPadding off 32 := by
  rw [constructorAssetStoreMemory, writeWord_sparse_read_preserved _ _ _ _
    (Or.inr ⟨he, by
      rw [constructorAssetFieldMemory_size _ _ _ (by decide), writeWord_sparse_size]
      omega⟩)]
  rw [(constructorAssetFieldMemory_prefix _ _ _ _).read _ hlo hhi
    (by rw [writeWord_sparse_size]; omega)]
  exact writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨hlo, hm⟩)

theorem constructorAssetLoopMemory_readField {c : ConstructorConfig} {i n j : Nat}
    (hi : i < n) (hn : n ≤ c.assetConfigs.length) (hj : j < 7) :
    (constructorAssetLoopMemory c n).readWithPadding (constructorAssetFree c i + 32 * j) 32 =
      (c.assetConfigs[i].word j).toByteArray := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [constructorAssetLoopMemory, dif_pos (by omega)]
    by_cases he : i = n
    · subst i
      rw [constructorAssetStoreMemory, writeWord_sparse_read_preserved _ _ _ _
        (Or.inr ⟨by
          unfold constructorAssetEntry constructorAssetFree constructorArrayEnd; omega, by
          rw [constructorAssetFieldMemory_size _ _ _ (by decide)]; omega⟩)]
      exact constructorAssetFieldMemory_readStored hj
    · rw [constructorAssetStoreMemory_readEarlier (by
        unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
        omega) (by unfold constructorAssetFree; omega) (by
        unfold constructorAssetEntry constructorAssetFree constructorArrayEnd; omega) (by
        rw [constructorAssetLoopMemory_size (by omega), if_neg (by omega)]
        unfold constructorAssetFree
        omega)]
      exact ih (by omega) (by omega)

theorem constructorDecodedMemory_assetEntry {c : ConstructorConfig} {i : Nat}
    (hi : i < c.assetConfigs.length) (hn : c.assetConfigs.length ≤ 24) :
    memLoad (UInt256.ofNat (constructorAssetEntry c i)) (constructorDecodedMemory c) =
      UInt256.ofNat (constructorAssetFree c i) := by
  have hp : (UInt256.ofNat (constructorAssetEntry c i)).toNat = constructorAssetEntry c i := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorAssetEntry constructorArrayBase constructorRecordBase
    change _ < 2^256
    omega
  apply mloadWordValue_of_readWithPadding
  · rw [hp, constructorDecodedMemory_size]
    unfold constructorAssetEntry constructorAssetFree constructorArrayEnd
    omega
  · rw [hp, constructorDecodedMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by unfold constructorAssetEntry constructorArrayBase; omega, by
        rw [constructorAssetLoopMemory_size (Nat.le_refl _), if_neg (by omega)]
        unfold constructorAssetEntry constructorAssetFree constructorArrayEnd
        omega⟩)]
    exact constructorAssetLoopMemory_readEntry hi (Nat.le_refl _)

theorem constructorDecodedMemory_assetField {c : ConstructorConfig} {i j : Nat}
    (hi : i < c.assetConfigs.length) (hn : c.assetConfigs.length ≤ 24) (hj : j < 7) :
    memLoad (UInt256.ofNat (constructorAssetFree c i + 32 * j)) (constructorDecodedMemory c) =
      c.assetConfigs[i].word j := by
  have hp : (UInt256.ofNat (constructorAssetFree c i + 32 * j)).toNat =
      constructorAssetFree c i + 32 * j := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    change _ < 2^256
    omega
  apply mloadWordValue_of_readWithPadding
  · rw [hp, constructorDecodedMemory_size]
    unfold constructorAssetFree
    omega
  · rw [hp, constructorDecodedMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inr ⟨by unfold constructorAssetFree constructorArrayEnd constructorArrayBase; omega, by
        rw [constructorAssetLoopMemory_size (Nat.le_refl _), if_neg (by omega)]
        unfold constructorAssetFree
        omega⟩)]
    exact constructorAssetLoopMemory_readField hi (Nat.le_refl _) hj

theorem ConstructorDataMemory.assetEntry {c : ConstructorConfig} {mem : ByteArray} {i : Nat}
    (hm : ConstructorDataMemory c mem) (hi : i < c.assetConfigs.length)
    (hn : c.assetConfigs.length ≤ 24) :
    memLoad (UInt256.ofNat (constructorAssetEntry c i)) mem =
      UInt256.ofNat (constructorAssetFree c i) := by
  have hp : (UInt256.ofNat (constructorAssetEntry c i)).toNat = constructorAssetEntry c i := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorAssetEntry constructorArrayBase constructorRecordBase
    change _ < 2^256
    omega
  rw [hm.words _ (by rw [hp]; unfold constructorAssetEntry constructorArrayBase; omega) (by
    rw [hp]; unfold constructorAssetEntry constructorAssetFree constructorArrayEnd; omega)]
  exact constructorDecodedMemory_assetEntry hi hn

theorem ConstructorDataMemory.assetField {c : ConstructorConfig} {mem : ByteArray} {i j : Nat}
    (hm : ConstructorDataMemory c mem) (hi : i < c.assetConfigs.length)
    (hn : c.assetConfigs.length ≤ 24) (hj : j < 7) :
    memLoad (UInt256.ofNat (constructorAssetFree c i + 32 * j)) mem =
      c.assetConfigs[i].word j := by
  have hp : (UInt256.ofNat (constructorAssetFree c i + 32 * j)).toNat =
      constructorAssetFree c i + 32 * j := by
    apply UInt256.toNat_ofNat_of_lt
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    change _ < 2^256
    omega
  rw [hm.words _ (by
    rw [hp]; unfold constructorAssetFree constructorArrayEnd constructorArrayBase; omega) (by
    rw [hp]; unfold constructorAssetFree; omega)]
  exact constructorDecodedMemory_assetField hi hn hj

end Benchmarks.CompoundIII.Comet
