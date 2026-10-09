import Benchmarks.CompoundIII.Comet.ConstructorRuntimeEvm
import Benchmarks.CompoundIII.Comet.ConstructorAssetsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables

namespace Benchmarks.CompoundIII.Comet

def constructorFinalMemory (c : ConstructorConfig) (w : UInt256)
    (out feed factoryOut assetOut : ByteArray) : ByteArray :=
  writeWord (constructorFactoryReturnMemory (constructorAssetsInputMemory c w out feed factoryOut)
    assetOut (UInt256.ofNat (constructorAssetsPtr c))) 896 (calldataWord assetOut 0)

theorem createAssetListEvmMemory_prefix {c : ConstructorConfig} {mem : ByteArray} {ptr : Nat}
    (hp : ptr + 68 < 2^64) (i : Nat) :
    MemoryPrefix mem (createAssetListEvmMemory c mem ptr i) ptr := by
  induction i with
  | zero =>
    unfold createAssetListEvmMemory createAssetListHeadMemory callTwoWordMemory callWordMemory
    have hpn : (UInt256.ofNat ptr).toNat = ptr :=
      UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
    have hadd (n : Nat) (hn : n ≤ 68) :
        (UInt256.ofNat ptr + UInt256.ofNat n).toNat = ptr + n := by
      rw [uadd_word_ofNat_toNat _ _ (by rw [hpn]; change _ < 2^256; omega), hpn]
    rw [hpn, hadd 4 (by decide), hadd 36 (by decide)]
    exact ((memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))).trans
        (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  | succ i ih =>
    rw [createAssetListEvmMemory]
    split
    · exact ih.trans ((constructorAssetFieldMemory_prefix _ _ _ _).mono (by omega))
    · exact ih

theorem constructorFinalMemory_prefix {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut assetOut : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size)
    (hf : factoryOut.size < UInt256.size) (ha : assetOut.size < UInt256.size) :
    MemoryPrefix (constructorFactoryBaseMemory c w out feed)
      (constructorFinalMemory c w out feed factoryOut assetOut) 896 := by
  have hflo : 896 ≤ (constructorFactoryPtr c).toNat := by
    rw [constructorFactoryPtr_toNat hn]
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    omega
  have halo : 896 ≤ constructorAssetsPtr c := by
    unfold constructorAssetsPtr constructorAssetFree constructorArrayEnd constructorArrayBase
      constructorRecordBase
    omega
  have h1 : MemoryPrefix (constructorFactoryBaseMemory c w out feed)
      (constructorFactoryInputMemory c w out feed) 896 :=
    memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl hflo)
  have h2 := (callOutput32_prefix (constructorFactoryInputMemory c w out feed) factoryOut
    (constructorFactoryPtr c) hf
      (by rw [constructorFactoryInputMemory_size hn hout hfeed])).mono hflo
  have h3 : MemoryPrefix (constructorFactoryInputMemory c w out feed)
      (constructorAssetsBaseMemory c w out feed factoryOut) 896 :=
    h2.trans (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))
  have h4 : MemoryPrefix (constructorAssetsBaseMemory c w out feed factoryOut)
      (constructorAssetsInputMemory c w out feed factoryOut) 896 :=
    (createAssetListEvmMemory_prefix (by
      have h := constructorAssetsPtr_fits hn; omega) c.assetConfigs.length).mono halo
  have hmem : (UInt256.ofNat (constructorAssetsPtr c)).toNat + 32 ≤
      (constructorAssetsInputMemory c w out feed factoryOut).size := by
    rw [constructorAssetsPtr_toNat hn]
    have hh := constructorAssetsInputMemory_size
      (w := w) (out := out) (feed := feed) (factoryOut := factoryOut) hn
    omega
  have h5 := (callOutput32_prefix (constructorAssetsInputMemory c w out feed factoryOut)
    assetOut (UInt256.ofNat (constructorAssetsPtr c)) ha hmem).mono
      (show 896 ≤ (UInt256.ofNat (constructorAssetsPtr c)).toNat by
        rw [constructorAssetsPtr_toNat hn]; exact halo)
  exact (((((h1.trans h3).trans h4).trans h5).trans
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))).trans
      (memoryPrefix_sparse_writeWord _ 896 _ _ (Or.inl (le_refl _))))

def constructorImmutableValues (c : ConstructorConfig) (w assetList : UInt256) : List UInt256 :=
  [constructorRecordWord c 0, constructorRecordWord c 1, constructorRecordWord c 2,
    constructorRecordWord c 3, constructorRecordWord c 4, constructorRecordWord c 5,
    constructorRateWord c 6, constructorRateWord c 7, constructorRateWord c 8,
    constructorRecordWord c 9, constructorRateWord c 10, constructorRateWord c 11,
    constructorRateWord c 12, constructorRecordWord c 13, constructorScaleWord w,
    constructorRecordWord c 14, constructorRecordWord c 15, constructorRecordWord c 16,
    constructorRecordWord c 17, constructorRecordWord c 18, constructorRecordWord c 19, w,
    UInt256.ofNat c.assetConfigs.length,
    UInt256.div (constructorScaleWord w) (UInt256.ofNat 1000000), assetList]

-- LIBRARY CANDIDATE: read a word stored at a bounded natural offset.
theorem memLoad_writeWord_ofNat_self (mem : ByteArray) (off : Nat) (word : UInt256)
    (hoff : off < UInt256.size) : memLoad (UInt256.ofNat off) (writeWord mem off word) = word := by
  have h := memLoad_writeWord_self mem (UInt256.ofNat off) word
  rwa [UInt256.toNat_ofNat_of_lt hoff] at h

set_option maxHeartbeats 800000 in
theorem constructorFinalMemory_word {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut assetOut : ByteArray} {i : Nat} (hi : i < 25)
    (hn : c.assetConfigs.length ≤ 24) (hout : out.size < UInt256.size)
    (hfeed : feed.size < UInt256.size) (hf : factoryOut.size < UInt256.size)
    (ha : assetOut.size < UInt256.size) :
    memLoad (UInt256.ofNat (128 + 32 * i))
      (constructorFinalMemory c w out feed factoryOut assetOut) =
      (constructorImmutableValues c w (calldataWord assetOut 0)).getD i ⟨0⟩ := by
  by_cases hlast : i = 24
  · subst i
    exact memLoad_writeWord_ofNat_self _ 896 _ (by decide)
  have hlow := constructorFinalMemory_prefix (w := w) hn hout hfeed hf ha
  rw [memoryPrefix_load hlow
    (by rw [UInt256.toNat_ofNat_of_lt (show 128 + 32 * i < UInt256.size by
      change _ < 2^256; omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (show 128 + 32 * i < UInt256.size by
      change _ < 2^256; omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (show 128 + 32 * i < UInt256.size by
      change _ < 2^256; omega), constructorFactoryBaseMemory_size hn hout hfeed,
      constructorFactoryPtr_toNat hn]
        unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
        omega)]
  have hbase : 928 ≤ (constructorPriceFeedReturnMemory c out feed).size := by
    have hm := ConstructorDataMemory.priceFeed (c := c) (by
      have h := constructorAssetsPtr_fits hn
      unfold constructorAssetsPtr at h
      omega) hout hfeed
    have hp := hm.present
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase at hp
    omega
  have hi : i < 24 := by omega
  interval_cases i <;>
    simp (disch := (first | omega | decide | (simp (disch := decide) only
      [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
      [constructorFactoryBaseMemory, constructorRemainingImmMemory, constructorBorrowMemory,
        constructorSupplyMemory, constructorRewardMemory, constructorScaleMemory,
        constructorInitialImmMemory, Nat.reduceMul, Nat.reduceAdd,
        memLoad_writeWord_ofNat_self, memLoad_writeWord_preserved, constructorImmutableValues,
        List.getD_cons_zero, List.getD_cons_succ]

end Benchmarks.CompoundIII.Comet
