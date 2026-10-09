import Benchmarks.CompoundIII.Comet.ConstructorAssetEnter
import Benchmarks.CompoundIII.Comet.AssetStructMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def ConstructorAsset.word (a : ConstructorAsset) (j : Nat) : UInt256 :=
  a.words.getD j ⟨0⟩

theorem ConstructorAsset.words_length (a : ConstructorAsset) : a.words.length = 7 := rfl

theorem constructorAssetWords_get (assets : List ConstructorAsset) (i j : Nat)
    (hi : i < assets.length) (hj : j < 7) :
    (assets.flatMap ConstructorAsset.words)[7 * i + j]? = some (assets[i].word j) := by
  induction assets generalizing i with
  | nil => simp at hi
  | cons a assets ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [ConstructorAsset.words_length]; exact hj),
        List.getElem?_eq_getElem (by rw [ConstructorAsset.words_length]; exact hj),
        List.getElem_eq_getD ⟨0⟩]
      rfl
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [ConstructorAsset.words_length]; omega),
        ConstructorAsset.words_length, show 7 * (i + 1) + j - 7 = 7 * i + j by omega]
      exact ih i (by simpa using hi)

theorem constructorAssetWord_argument {c : ConstructorConfig} {i j : Nat}
    (hi : i < c.assetConfigs.length) (hj : j < 7) :
    c.argumentWords[23 + 7 * i + j]? = some (c.assetConfigs[i].word j) := by
  have hs : ([(⟨32⟩ : UInt256)] ++ c.scalars.map ScalarReturn.word ++
      [(⟨672⟩ : UInt256), UInt256.ofNat c.assetConfigs.length]).length = 23 := rfl
  rw [ConstructorConfig.argumentWords, List.getElem?_append_right (by rw [hs]; omega), hs,
    show 23 + 7 * i + j - 23 = 7 * i + j by omega]
  exact constructorAssetWords_get _ _ _ hi hj

theorem constructorCopiedMemory_assetWord {c : ConstructorConfig} {i j : Nat}
    (hi : i < c.assetConfigs.length) (hj : j < 7)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    memLoad (UInt256.ofNat (1664 + 224 * i + 32 * j)) (constructorCopiedMemory c) =
      c.assetConfigs[i].word j := by
  obtain ⟨hindex, hword⟩ := List.getElem?_eq_some_iff.mp (constructorAssetWord_argument hi hj)
  have hr := constructorCopiedMemory_load c (23 + 7 * i + j) hindex hsize
  rw [hword, show 928 + 32 * (23 + 7 * i + j) = 1664 + 224 * i + 32 * j by omega] at hr
  exact hr

def constructorAssetFieldMemory (mem : ByteArray) (dst : Nat) (a : ConstructorAsset) :
    Nat → ByteArray
  | 0 => mem
  | j + 1 => writeWord (constructorAssetFieldMemory mem dst a j) (dst + 32 * j) (a.word j)

theorem constructorAssetFieldMemory_prefix (mem : ByteArray) (dst : Nat)
    (a : ConstructorAsset) (n : Nat) :
    MemoryPrefix mem (constructorAssetFieldMemory mem dst a n) dst := by
  induction n with
  | zero => exact .refl _ _
  | succ n ih =>
    exact ih.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))

theorem constructorAssetFieldMemory_size (mem : ByteArray) (dst : Nat)
    (a : ConstructorAsset) {n : Nat} (hn : 0 < n) :
    (constructorAssetFieldMemory mem dst a n).size = max mem.size (dst + 32 * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [constructorAssetFieldMemory, writeWord_sparse_size]
    cases n with
    | zero => rfl
    | succ n => rw [ih (by omega)]; omega

theorem constructorAssetFieldMemory_load {mem : ByteArray} {dst src : Nat}
    {a : ConstructorAsset} {n j : Nat} (hj : j < 7) (hsrc : 96 ≤ src)
    (hdisj : src + 224 ≤ dst) (hin : src + 224 ≤ mem.size)
    (hsmall : src + 224 < UInt256.size) :
    memLoad (UInt256.ofNat (src + 32 * j)) (constructorAssetFieldMemory mem dst a n) =
      memLoad (UInt256.ofNat (src + 32 * j)) mem := by
  apply memoryPrefix_load (constructorAssetFieldMemory_prefix _ _ _ _)
  all_goals rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega

theorem constructorArrayHeaderMemory_prefix (c : ConstructorConfig) :
    MemoryPrefix (constructorCopiedMemory c) (constructorArrayHeaderMemory c)
      (constructorRecordBase c) := by
  apply (constructorScalarMemory_prefix c 20).trans
  exact (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by unfold constructorArrayBase; omega)))

theorem constructorArrayHeaderMemory_size (c : ConstructorConfig) :
    (constructorArrayHeaderMemory c).size = constructorArrayBase c + 32 := by
  rw [constructorArrayHeaderMemory, constructorArrayMemory, writeWord_sparse_size,
    writeWord_sparse_size, constructorScalarMemory_size]
  unfold constructorArrayBase constructorRecordBase
  omega

theorem constructorArrayHeaderMemory_readFree (c : ConstructorConfig) :
    (constructorArrayHeaderMemory c).readWithPadding 64 32 =
      (UInt256.ofNat (constructorArrayEnd c)).toByteArray := by
  rw [constructorArrayHeaderMemory, writeWord_sparse_read_preserved _ _ _ _
    (Or.inl ⟨by unfold constructorArrayBase constructorRecordBase; omega, by
      rw [constructorArrayMemory, writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem constructorArrayHeaderMemory_free (c : ConstructorConfig) :
    memLoad ⟨64⟩ (constructorArrayHeaderMemory c) = UInt256.ofNat (constructorArrayEnd c) := by
  apply mloadWordValue_of_readWithPadding
  · rw [constructorArrayHeaderMemory_size]
    change 64 < _
    unfold constructorArrayBase constructorRecordBase
    omega
  · exact constructorArrayHeaderMemory_readFree c

end Benchmarks.CompoundIII.Comet
