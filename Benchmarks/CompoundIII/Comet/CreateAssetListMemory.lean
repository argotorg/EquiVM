import Benchmarks.CompoundIII.Comet.CreateAssetListEncoder
import Benchmarks.CompoundIII.Comet.CreateAssetListSyntax
import Benchmarks.CompoundIII.Comet.CallWordsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def createAssetListSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 3121986001) (UInt256.ofNat 224)

def createAssetListHeadMemory (c : ConstructorConfig) (mem : ByteArray) (ptr : Nat) : ByteArray :=
  callTwoWordMemory mem (UInt256.ofNat ptr) createAssetListSelectorWord
    (UInt256.ofNat 32) (UInt256.ofNat c.assetConfigs.length)

def createAssetListEvmMemory (c : ConstructorConfig) (mem : ByteArray) (ptr : Nat) :
    Nat → ByteArray
  | 0 => createAssetListHeadMemory c mem ptr
  | i + 1 => if hi : i < c.assetConfigs.length then
      constructorAssetFieldMemory (createAssetListEvmMemory c mem ptr i)
        (ptr + 68 + 224 * i) c.assetConfigs[i] 7
    else createAssetListEvmMemory c mem ptr i

theorem createAssetListPayload_size {assets : List ConstructorAsset} {i : Nat}
    (hi : i ≤ assets.length) : (createAssetListPayload assets i).size = 68 + 224 * i := by
  have hw (xs : List ConstructorAsset) :
      (xs.flatMap ConstructorAsset.words).length = 7 * xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, ConstructorAsset.words_length,
        ih, List.length_cons]
      omega
  have hh (n : Nat) : (createAssetListHeader n).size = 68 := by
    change ([186, 21, 185, 209] ++ EVM.Word.toBytesBE (UInt256.ofNat 32) ++
      EVM.Word.toBytesBE (UInt256.ofNat n)).toArray.size = 68
    simp only [List.size_toArray, List.length_append, List.length_cons, List.length_nil,
      word_toBytesBE_length_32]
  rw [createAssetListPayload, ByteArray.size_append, hh, wordBytes_size, hw,
    List.length_take, Nat.min_eq_left hi]
  omega

theorem createAssetListHeadMemory_size {c : ConstructorConfig} {mem : ByteArray} {ptr : Nat}
    (hp : ptr + 68 < 2^64) :
    (createAssetListHeadMemory c mem ptr).size = max mem.size (ptr + 68) := by
  have hptr := UInt256.toNat_ofNat_of_lt (show ptr < UInt256.size by change _ < 2^256; omega)
  rw [createAssetListHeadMemory, callTwoWordMemory_size (by rw [hptr]; change _ < 2^256; omega),
    hptr]

theorem createAssetListHeadMemory_data {c : ConstructorConfig} {mem : ByteArray} {ptr : Nat}
    (hm : ConstructorDataMemory c mem) (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr)
    (hp : ptr + 68 < 2^64) : ConstructorDataMemory c (createAssetListHeadMemory c mem ptr) := by
  have hptr := UInt256.toNat_ofNat_of_lt (show ptr < UInt256.size by change _ < 2^256; omega)
  have hadd (n : Nat) (hn : n ≤ 68) :
      (UInt256.ofNat ptr + UInt256.ofNat n).toNat = ptr + n := by
    rw [uadd_word_ofNat_toNat _ _ (by rw [hptr]; change _ < 2^256; omega), hptr]
  unfold createAssetListHeadMemory callTwoWordMemory callWordMemory
  rw [hptr, hadd 4 (by decide), hadd 36 (by decide)]
  exact ((hm.writeAbove _ hlo).writeAbove _ (by omega)).writeAbove _ (by omega)

theorem createAssetListHeadMemory_payload {c : ConstructorConfig} {mem : ByteArray} {ptr : Nat}
    (hp : ptr + 68 < 2^64) :
    (createAssetListHeadMemory c mem ptr).readWithPadding ptr 68 =
      createAssetListHeader c.assetConfigs.length := by
  have hptr := UInt256.toNat_ofNat_of_lt (show ptr < UInt256.size by change _ < 2^256; omega)
  have hs : createAssetListSelectorWord.toByteArray.extract 0 4 =
      ([186, 21, 185, 209] : List UInt8).toByteArray := by decide +kernel
  have hr := callTwoWordMemory_payload (mem := mem) (ptr := UInt256.ofNat ptr)
    (selector := createAssetListSelectorWord) (first := UInt256.ofNat 32)
    (second := UInt256.ofNat c.assetConfigs.length) (by rw [hptr]; exact hp)
  rw [hptr, hs] at hr
  rw [createAssetListHeadMemory, hr]
  rw [createAssetListHeader, mk_toArray_eq, list_toByteArray_append, list_toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, word_toBytesBE_toByteArray_eq_toByteArray]

theorem constructorAssetFieldMemory_data {c : ConstructorConfig} {mem : ByteArray}
    {ptr : Nat} (hm : ConstructorDataMemory c mem) (a : ConstructorAsset) (n : Nat)
    (hp : constructorAssetFree c c.assetConfigs.length ≤ ptr) :
    ConstructorDataMemory c (constructorAssetFieldMemory mem ptr a n) := by
  induction n with
  | zero => exact hm
  | succ n ih => exact ih.writeAbove _ (by omega)

theorem constructorAssetFieldMemory_payload {mem : ByteArray} {ptr len : Nat}
    {a : ConstructorAsset} {n : Nat} (hn : n ≤ 7) (hpos : 0 < len)
    (hm : ptr + len ≤ mem.size) (hp : ptr + len + 224 < 2^64) :
    (constructorAssetFieldMemory mem (ptr + len) a n).readWithPadding ptr (len + 32 * n) =
      mem.readWithPadding ptr len ++ wordBytes (a.words.take n) := by
  induction n with
  | zero => simp only [constructorAssetFieldMemory, Nat.mul_zero, Nat.add_zero,
      List.take_zero, wordBytes, ByteArray.append_empty]
  | succ n ih =>
    have hs : ptr + (len + 32 * n) ≤
        (constructorAssetFieldMemory mem (ptr + len) a n).size := by
      cases n with
      | zero => exact hm
      | succ n => rw [constructorAssetFieldMemory_size _ _ _ (by omega)]; omega
    rw [constructorAssetFieldMemory,
      show ptr + len + 32 * n = ptr + (len + 32 * n) by omega,
      show len + 32 * (n + 1) = (len + 32 * n) + 32 by omega,
      memoryPayload_append_word (by omega) hs (by omega), ih (by omega),
      List.take_succ_eq_append_getElem (by rw [ConstructorAsset.words_length]; omega),
      wordBytes_append]
    simp only [wordBytes, ByteArray.append_empty, ByteArray.append_assoc, ConstructorAsset.word]
    rw [List.getD_eq_getElem a.words (⟨0⟩ : UInt256)
      (by rw [ConstructorAsset.words_length]; omega)]

theorem createAssetListEvmMemory_size {c : ConstructorConfig} {mem : ByteArray} {ptr i : Nat}
    (hi : i ≤ c.assetConfigs.length) (hp : ptr + 68 < 2^64) :
    (createAssetListEvmMemory c mem ptr i).size = max mem.size (ptr + 68 + 224 * i) := by
  induction i with
  | zero => exact createAssetListHeadMemory_size hp
  | succ i ih =>
    rw [createAssetListEvmMemory, dif_pos (by omega),
      constructorAssetFieldMemory_size _ _ _ (by decide), ih (by omega)]
    omega

theorem createAssetListEvmMemory_data {c : ConstructorConfig} {mem : ByteArray} {ptr i : Nat}
    (hm : ConstructorDataMemory c mem) (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr)
    (hp : ptr + 68 < 2^64) :
    ConstructorDataMemory c (createAssetListEvmMemory c mem ptr i) := by
  induction i with
  | zero => exact createAssetListHeadMemory_data hm hlo hp
  | succ i ih =>
    rw [createAssetListEvmMemory]
    split
    · exact constructorAssetFieldMemory_data ih _ _ (by omega)
    · exact ih

theorem createAssetListEvmMemory_payload {c : ConstructorConfig} {mem : ByteArray} {ptr i : Nat}
    (hi : i ≤ c.assetConfigs.length) (hp : ptr + 68 + 224 * c.assetConfigs.length < 2^64) :
    (createAssetListEvmMemory c mem ptr i).readWithPadding ptr (68 + 224 * i) =
      createAssetListPayload c.assetConfigs i := by
  induction i with
  | zero =>
    exact (createAssetListHeadMemory_payload (c := c) (mem := mem) (ptr := ptr)
      (by omega)).trans (createAssetListPayload_zero _).symm
  | succ i ih =>
    rw [createAssetListEvmMemory, dif_pos (by omega), createAssetListPayload_succ (by omega)]
    have hr := constructorAssetFieldMemory_payload
      (mem := createAssetListEvmMemory c mem ptr i) (ptr := ptr) (len := 68 + 224 * i)
      (a := c.assetConfigs[i]) (n := 7) (by decide) (by omega)
      (by rw [createAssetListEvmMemory_size (by omega) (by omega)]; omega) (by omega)
    rw [show ptr + (68 + 224 * i) = ptr + 68 + 224 * i by omega,
      show 68 + 224 * i + 32 * 7 = 68 + 224 * (i + 1) by omega,
      List.take_of_length_le (by rw [ConstructorAsset.words_length]), ih (by omega)] at hr
    exact hr

end Benchmarks.CompoundIII.Comet
