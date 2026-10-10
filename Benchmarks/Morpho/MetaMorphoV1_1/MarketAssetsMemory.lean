import Benchmarks.Morpho.MetaMorphoV1_1.MarketAssetsRoutines

/-! Market memory after adding the same interest amount to borrow and supply assets. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketAssetsMemory (mem : ByteArray) (ptr src interest : UInt256) (market : ByteArray) :
    ByteArray :=
  writeWord (marketAssetsInterimMemory mem ptr src interest market) src.toNat
    (calldataWord market 0 + interest)

theorem marketAssetsMemory_size {mem market : ByteArray} {ptr src interest : UInt256}
    (hlo : 96 ≤ src.toNat) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨64⟩) :
    (marketAssetsMemory mem ptr src interest market).size = max mem.size (ptr.toNat + 128) := by
  have hn := nextCursor64_toNat hfit
  have hadd : (src + UInt256.ofNat 64).toNat = src.toNat + 64 :=
    uadd_word_ofNat_toNat src 64 (by have h : ptr.toNat < UInt256.size := ptr.val.isLt; omega)
  rw [marketAssetsMemory, writeWord_sparse_size, marketAssetsInterimMemory,
    uint128CastMemory_size _ _ (by rw [hn]; omega), marketBorrowMemory,
    castStoreMemory_size _ _ _ _ (by omega) (by rw [hadd]; omega), hn]
  omega

theorem marketAssetsMemory_free {mem market : ByteArray} {ptr src interest : UInt256}
    (hlo : 96 ≤ src.toNat) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨64⟩) :
    memLoad ⟨64⟩ (marketAssetsMemory mem ptr src interest market) =
      nextCursor (nextCursor ptr ⟨64⟩) ⟨64⟩ := by
  have hn := nextCursor64_toNat hfit
  have hp : 96 ≤ (nextCursor ptr ⟨64⟩).toNat := by rw [hn]; omega
  rw [marketAssetsMemory, memLoad_write_above _ _ _ _
    (by rw [marketAssetsInterimMemory, uint128CastMemory_size _ _ hp]
        change 64 + 32 ≤ _; omega) hlo]
  exact uint128CastMemory_free _ _ hp

theorem marketAssetsMemory_prefix {mem market : ByteArray} {ptr src interest : UInt256}
    (hsep : src.toNat + 192 ≤ ptr.toNat) (hfit : allocationFits ptr ⟨64⟩) :
    MemoryPrefix mem (marketAssetsMemory mem ptr src interest market) src.toNat := by
  have hn := nextCursor64_toNat hfit
  have hadd : (src + UInt256.ofNat 64).toNat = src.toNat + 64 :=
    uadd_word_ofNat_toNat src 64 (by have h : ptr.toNat < UInt256.size := ptr.val.isLt; omega)
  exact ((castStoreMemory_prefix mem ptr (src + UInt256.ofNat 64)
      (calldataWord market 64 + interest) (by rw [hadd]; omega)).mono (by rw [hadd]; omega)).trans
    (((uint128CastMemory_prefix _ _).mono (by rw [hn]; omega)).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))))

theorem marketAssetsMemory_preserves {mem market : ByteArray} {ptr src interest read : UInt256}
    (hfit : allocationFits ptr ⟨64⟩) (hlo : 96 ≤ read.toNat)
    (hptr : read.toNat + 32 ≤ ptr.toNat) (hin : read.toNat + 32 ≤ mem.size)
    (hb : read.toNat + 32 ≤ (src + UInt256.ofNat 64).toNat ∨
      (src + UInt256.ofNat 64).toNat + 32 ≤ read.toNat)
    (hs : read.toNat + 32 ≤ src.toNat ∨ src.toNat + 32 ≤ read.toNat) :
    memLoad read (marketAssetsMemory mem ptr src interest market) = memLoad read mem := by
  have hn := nextCursor64_toNat hfit
  have hm : mem.size ≤ (marketBorrowMemory mem ptr src interest market).size := by
    rw [marketBorrowMemory, castStoreMemory, writeWord_sparse_size]
    have h := (uint128CastMemory_prefix mem ptr).size
    omega
  have hm' : mem.size ≤ (marketAssetsInterimMemory mem ptr src interest market).size :=
    le_trans hm (uint128CastMemory_prefix _ _).size
  have hw : memLoad read (marketAssetsMemory mem ptr src interest market) =
      memLoad read (marketAssetsInterimMemory mem ptr src interest market) :=
    memLoad_write_disjoint _ _ _ _ (by omega) hs
  rw [hw, marketAssetsInterimMemory, uint128CastMemory_load hlo (by rw [hn]; omega) (by omega)]
  exact castStoreMemory_preserves hlo hptr hin hb

theorem marketAssetsMemory_supply {mem market : ByteArray} {ptr src interest : UInt256} :
    memLoad src (marketAssetsMemory mem ptr src interest market) =
      calldataWord market 0 + interest := by
  exact memLoad_write_same _ _ _ _ rfl

theorem marketAssetsMemory_borrow {mem market : ByteArray} {ptr src interest : UInt256}
    (hlo : 96 ≤ src.toNat) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hfit : allocationFits ptr ⟨64⟩) :
    memLoad (src + UInt256.ofNat 64) (marketAssetsMemory mem ptr src interest market) =
      calldataWord market 64 + interest := by
  have hn := nextCursor64_toNat hfit
  have hadd : (src + UInt256.ofNat 64).toNat = src.toNat + 64 :=
    uadd_word_ofNat_toNat src 64 (by have h : ptr.toNat < UInt256.size := ptr.val.isLt; omega)
  have hm : (src + UInt256.ofNat 64).toNat + 32 ≤
      (marketBorrowMemory mem ptr src interest market).size := by
    rw [marketBorrowMemory, castStoreMemory_size _ _ _ _ (by omega) (by rw [hadd]; omega)]
    rw [hadd]
    omega
  have hr : memLoad (src + UInt256.ofNat 64)
      (marketAssetsInterimMemory mem ptr src interest market) =
        calldataWord market 64 + interest := by
    rw [marketAssetsInterimMemory,
      uint128CastMemory_load (by rw [hadd]; omega) (by rw [hadd, hn]; omega) hm]
    exact castStoreMemory_field _ _ _ _
  have hw : memLoad (src + UInt256.ofNat 64) (marketAssetsMemory mem ptr src interest market) =
      memLoad (src + UInt256.ofNat 64) (marketAssetsInterimMemory mem ptr src interest market) :=
    memLoad_write_disjoint _ _ _ _
      (by have h : (marketBorrowMemory mem ptr src interest market).size ≤
            (marketAssetsInterimMemory mem ptr src interest market).size :=
              (uint128CastMemory_prefix _ _).size
          omega)
      (.inr (by rw [hadd]; omega))
  exact hw.trans hr

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
