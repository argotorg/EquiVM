import Benchmarks.CompoundIII.Comet.ConstructorAssetFields

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def constructorAssetFree (c : ConstructorConfig) (i : Nat) : Nat :=
  constructorArrayEnd c + 224 * i

def constructorAssetEntry (c : ConstructorConfig) (i : Nat) : Nat :=
  constructorArrayBase c + 32 + 32 * i

def constructorAssetStoreMemory (mem : ByteArray) (dst entry : Nat) (a : ConstructorAsset) :
    ByteArray :=
  writeWord (constructorAssetFieldMemory (writeWord mem 64 (UInt256.ofNat (dst + 224)))
    dst a 7) entry (UInt256.ofNat dst)

def constructorAssetLoopMemory (c : ConstructorConfig) : Nat → ByteArray
  | 0 => constructorArrayHeaderMemory c
  | i + 1 => if hi : i < c.assetConfigs.length then
      constructorAssetStoreMemory (constructorAssetLoopMemory c i) (constructorAssetFree c i)
        (constructorAssetEntry c i) c.assetConfigs[i]
    else constructorAssetLoopMemory c i

theorem constructorAssetStoreMemory_prefix (mem : ByteArray) (dst entry : Nat)
    (a : ConstructorAsset) {limit : Nat} (hdst : limit ≤ dst) (hentry : limit ≤ entry) :
    MemoryPrefix mem (constructorAssetStoreMemory mem dst entry a) limit := by
  apply (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
  apply ((constructorAssetFieldMemory_prefix _ _ _ _).mono hdst).trans
  exact memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl hentry)

theorem constructorAssetStoreMemory_size (mem : ByteArray) (dst entry : Nat)
    (a : ConstructorAsset) (hdst : 96 ≤ dst) (hentry : entry + 32 ≤ dst) :
    (constructorAssetStoreMemory mem dst entry a).size = max mem.size (dst + 224) := by
  rw [constructorAssetStoreMemory, writeWord_sparse_size,
    constructorAssetFieldMemory_size _ _ _ (by decide), writeWord_sparse_size]
  omega

theorem constructorAssetFieldMemory_readFree {mem : ByteArray} {dst : Nat}
    (a : ConstructorAsset) (n : Nat) (hdst : 96 ≤ dst) (hmem : 96 ≤ mem.size) :
    (constructorAssetFieldMemory mem dst a n).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [constructorAssetFieldMemory, writeWord_sparse_read_preserved _ _ _ _
      (Or.inl ⟨by omega, le_trans hmem (constructorAssetFieldMemory_prefix _ _ _ _).size⟩), ih]

theorem constructorAssetStoreMemory_readFree (mem : ByteArray) (dst entry : Nat)
    (a : ConstructorAsset) (hdst : 96 ≤ dst) (hentry : 96 ≤ entry) :
    (constructorAssetStoreMemory mem dst entry a).readWithPadding 64 32 =
      (UInt256.ofNat (dst + 224)).toByteArray := by
  rw [constructorAssetStoreMemory, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨hentry, by
      rw [constructorAssetFieldMemory_size _ _ _ (by decide), writeWord_sparse_size]; omega⟩),
    constructorAssetFieldMemory_readFree _ _ hdst (by rw [writeWord_sparse_size]; omega)]
  exact writeWord_sparse_read_back _ _ _

theorem constructorAssetLoopMemory_prefix (c : ConstructorConfig) (i : Nat) :
    MemoryPrefix (constructorCopiedMemory c) (constructorAssetLoopMemory c i)
      (constructorRecordBase c) := by
  induction i with
  | zero => exact constructorArrayHeaderMemory_prefix c
  | succ i ih =>
    rw [constructorAssetLoopMemory]
    split
    · exact ih.trans (constructorAssetStoreMemory_prefix _ _ _ _
        (by unfold constructorAssetFree constructorArrayEnd constructorArrayBase; omega)
        (by unfold constructorAssetEntry constructorArrayBase; omega))
    · exact ih

theorem constructorAssetLoopMemory_size {c : ConstructorConfig} {i : Nat}
    (hi : i ≤ c.assetConfigs.length) :
    (constructorAssetLoopMemory c i).size =
      if i = 0 then constructorArrayBase c + 32 else constructorAssetFree c i := by
  induction i with
  | zero => exact constructorArrayHeaderMemory_size c
  | succ i ih =>
    rw [constructorAssetLoopMemory, dif_pos (by omega), constructorAssetStoreMemory_size]
    · rw [ih (by omega)]
      split <;> simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
      all_goals unfold constructorAssetFree constructorArrayEnd
      all_goals omega
    · unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
      omega
    · unfold constructorAssetEntry constructorAssetFree constructorArrayEnd
      omega

theorem constructorAssetLoopMemory_readFree {c : ConstructorConfig} {i : Nat}
    (hi : i ≤ c.assetConfigs.length) :
    (constructorAssetLoopMemory c i).readWithPadding 64 32 =
      (UInt256.ofNat (constructorAssetFree c i)).toByteArray := by
  cases i with
  | zero => exact constructorArrayHeaderMemory_readFree c
  | succ i =>
    rw [constructorAssetLoopMemory, dif_pos (by omega), constructorAssetStoreMemory_readFree]
    · rw [show constructorAssetFree c i + 224 = constructorAssetFree c (i + 1) by
        unfold constructorAssetFree; omega]
    · unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
      omega
    · unfold constructorAssetEntry constructorArrayBase constructorRecordBase
      omega

theorem constructorAssetLoopMemory_free {c : ConstructorConfig} {i : Nat}
    (hi : i ≤ c.assetConfigs.length) :
    memLoad ⟨64⟩ (constructorAssetLoopMemory c i) = UInt256.ofNat (constructorAssetFree c i) := by
  apply mloadWordValue_of_readWithPadding
  · have hh := (constructorAssetLoopMemory_prefix c i).size
    rw [constructorCopiedMemory_size] at hh
    change 64 < _
    omega
  · exact constructorAssetLoopMemory_readFree hi

theorem constructorAssetLoopMemory_load {c : ConstructorConfig} {i j : Nat}
    (hi : i < c.assetConfigs.length) (hj : j < 7)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (1664 + 224 * i + 32 * j)) (constructorAssetLoopMemory c i) =
      c.assetConfigs[i].word j := by
  rw [memoryPrefix_load (constructorAssetLoopMemory_prefix c i) (by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega) (by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]; unfold constructorRecordBase; omega) (by
    rw [UInt256.toNat_ofNat_of_lt (by omega), constructorCopiedMemory_size]; omega)]
  exact constructorCopiedMemory_assetWord hi hj hsize

end Benchmarks.CompoundIII.Comet
