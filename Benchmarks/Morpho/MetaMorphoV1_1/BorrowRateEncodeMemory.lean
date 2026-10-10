import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateCall
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory

/-! Preservation and the market-field writes in the rate-model call encoder. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: preserve a complete word-load window under an allocated-prefix relation.
theorem wordWindowPrefix_load {before after : ByteArray} {src : UInt256} {len limit : Nat}
    (hprefix : MemoryPrefix before after limit) (hlo : 96 ≤ src.toNat)
    (hmem : src.toNat + len ≤ before.size) (hlimit : src.toNat + len ≤ limit)
    (hfit : src.toNat + len < UInt256.size) :
    ∀ off, off + 32 ≤ len → memLoad (src + UInt256.ofNat off) after =
      memLoad (src + UInt256.ofNat off) before := by
  intro off hoff
  have hadd : (src + UInt256.ofNat off).toNat = src.toNat + off :=
    uadd_word_ofNat_toNat src off (by omega)
  simpa only [u256_ofNat_toNat] using hprefix.load_preserved
    (off := (src + UInt256.ofNat off).toNat) (by rw [hadd]; omega)
    (by rw [hadd]; omega) (by rw [hadd]; omega)
    (src + UInt256.ofNat off).val.isLt

def borrowRateFirstFiveMem (mem : ByteArray) (ptr : UInt256) (market : ByteArray) : ByteArray :=
  wordSequenceMemory mem (ptr.toNat + 164) ((marketWords market).take 5)

theorem borrowRateFirstFiveMemory {mem market : ByteArray} {src ptr : UInt256}
    (hmem : src.toNat + 192 ≤ mem.size) (hsep : src.toNat + 192 ≤ ptr.toNat)
    (hptr : ptr.toNat + 356 < UInt256.size) (hc : MarketChecks market)
    (hload : ∀ off, off + 32 ≤ 192 →
      memLoad (src + UInt256.ofNat off) mem = calldataWord market off) :
    metaMorphoV1_1_block_17114_memory (mem := mem) (x1 := ptr)
      (x2 := src + UInt256.ofNat 128) (x4 := src) = borrowRateFirstFiveMem mem ptr market := by
  have hs : src.toNat + 192 < UInt256.size := by omega
  have hadd (n : Nat) (hn : n ≤ 324) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (by omega)
  have hmask (off : Nat) (hfit : (calldataWord market off).toNat < 2 ^ 128) :
      UInt256.land (calldataWord market off)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1)) = calldataWord market off :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hfit
  have h0 : memLoad src mem = calldataWord market 0 := by
    simpa only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] using
      hload 0 (by decide)
  let m1 := writeWord mem (ptr.toNat + 164) (calldataWord market 0)
  have hm1 : src.toNat + 192 ≤ m1.size := by dsimp [m1]; rw [writeWord_sparse_size]; omega
  have hr1 := wordWindowRead_write (ptr.toNat + 164) (calldataWord market 0)
    hmem (by omega) hs hload
  let m2 := writeWord m1 (ptr.toNat + 196) (calldataWord market 32)
  have hm2 : src.toNat + 192 ≤ m2.size := by dsimp [m2]; rw [writeWord_sparse_size]; omega
  have hr2 := wordWindowRead_write (ptr.toNat + 196) (calldataWord market 32)
    hm1 (by omega) hs hr1
  let m3 := writeWord m2 (ptr.toNat + 228) (calldataWord market 64)
  have hm3 : src.toNat + 192 ≤ m3.size := by dsimp [m3]; rw [writeWord_sparse_size]; omega
  have hr3 := wordWindowRead_write (ptr.toNat + 228) (calldataWord market 64)
    hm2 (by omega) hs hr2
  have hr4 := wordWindowRead_write (ptr.toNat + 260) (calldataWord market 96)
    hm3 (by omega) hs hr3
  dsimp only [m1, m2, m3] at hr2 hr3 hr4
  have hwrite (m : ByteArray) (off : Nat) (w : UInt256) :
      w.toByteArray.write 0 m off 32 = writeWord m off w := rfl
  simp only [metaMorphoV1_1_block_17114_memory, hwrite, hadd 164 (by decide),
    hadd 196 (by decide), hadd 228 (by decide), hadd 260 (by decide), hadd 292 (by decide),
    h0, hmask 0 hc.2.1, hr1 32 (by decide), hmask 32 hc.2.2.1,
    hr2 64 (by decide), hmask 64 hc.2.2.2.1, hr3 96 (by decide), hmask 96 hc.2.2.2.2.1,
    hr4 128 (by decide), hmask 128 hc.2.2.2.2.2.1]
  simp only [borrowRateFirstFiveMem, marketWords, List.take, wordSequenceMemory,
    Nat.add_assoc, Nat.reduceAdd]

theorem borrowRateFirstFiveMem_prefix (mem : ByteArray) (ptr : UInt256) (market : ByteArray) :
    MemoryPrefix mem (borrowRateFirstFiveMem mem ptr market) ptr.toNat :=
  (wordSequenceMemory_prefix _ _ _).mono (by omega)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
