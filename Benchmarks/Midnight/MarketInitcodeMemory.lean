import Benchmarks.Midnight.MarketBytesMemory
import Benchmarks.Midnight.ByteCopyMemory
import Benchmarks.Midnight.MarketIdSource

/-! Concatenating the initialization prefix and market ABI bytes in runtime memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketInitcodeFirstMemory (mem : ByteArray) (root prefixPtr : UInt256) : ByteArray :=
  copyZeroMemory mem mem (prefixPtr.toNat + 32) (root.toNat + 32) 11

def marketInitcodeCopyMemory (mem : ByteArray) (root prefixPtr encoded : UInt256)
    (m : MarketData) : ByteArray :=
  let first := marketInitcodeFirstMemory mem root prefixPtr
  copyZeroMemory first first (encoded.toNat + 32) (root.toNat + 43) m.encodingSize

def marketInitcodeMemory (mem : ByteArray) (root prefixPtr encoded : UInt256)
    (m : MarketData) : ByteArray :=
  writeWord (writeWord (marketInitcodeCopyMemory mem root prefixPtr encoded m) root.toNat
    (UInt256.ofNat (11 + m.encodingSize))) 64 (root + UInt256.ofNat (m.encodingSize + 64))

theorem marketInitcodeFirstMemory_size (mem : ByteArray) (root prefixPtr : UInt256)
    (hp : prefixPtr.toNat + 43 ≤ mem.size) :
    (marketInitcodeFirstMemory mem root prefixPtr).size = max mem.size (root.toNat + 75) := by
  rw [marketInitcodeFirstMemory, copyZeroMemory_size _ _ _ _ _ (by decide) (by omega)]

theorem marketInitcodeMemory_prefix (mem : ByteArray) (root prefixPtr encoded : UInt256)
    (m : MarketData) (hp : prefixPtr.toNat + 43 ≤ mem.size)
    (he : encoded.toNat + 32 + m.encodingSize ≤ mem.size) :
    MemoryPrefix mem (marketInitcodeMemory mem root prefixPtr encoded m) root.toNat := by
  have hfirst := copyZeroMemory_prefix mem mem (prefixPtr.toNat + 32) (root.toNat + 32) 11
    root.toNat (by decide) (by omega) (by omega)
  have hsecond := copyZeroMemory_prefix (marketInitcodeFirstMemory mem root prefixPtr)
    (marketInitcodeFirstMemory mem root prefixPtr) (encoded.toNat + 32) (root.toNat + 43)
    m.encodingSize root.toNat (by dsimp only [MarketData.encodingSize]; omega)
    (he.trans hfirst.size) (by omega)
  exact ((hfirst.trans hsecond).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl))).trans
    (memoryPrefix_writeWord _ 64 _ _ (Or.inr (by decide)))

theorem marketInitcodeMemory_free (mem : ByteArray) (root prefixPtr encoded : UInt256)
    (m : MarketData) :
    memLoad (UInt256.ofNat 64) (marketInitcodeMemory mem root prefixPtr encoded m) =
      root + UInt256.ofNat (m.encodingSize + 64) := memLoad_writeWord _ _ _

theorem marketInitcodeMemory_length (mem : ByteArray) {root prefixPtr encoded : UInt256}
    (m : MarketData) (hroot : 96 ≤ root.toNat) :
    memLoad root (marketInitcodeMemory mem root prefixPtr encoded m) =
      UInt256.ofNat (11 + m.encodingSize) := by
  rw [marketInitcodeMemory, memLoad_writeWord_preserved]
  · exact memLoad_writeWord _ _ _
  · rw [writeWord_sparse_size]; omega
  · right; change 64 + 32 ≤ root.toNat; exact hroot

theorem marketInitcodeMemory_size (mem : ByteArray) (root prefixPtr encoded : UInt256)
    (m : MarketData) (hp : prefixPtr.toNat + 43 ≤ mem.size)
    (he : encoded.toNat + 32 + m.encodingSize ≤ mem.size) :
    root.toNat + 75 + m.encodingSize ≤ (marketInitcodeMemory mem root prefixPtr encoded m).size := by
  have hf := marketInitcodeFirstMemory_size mem root prefixPtr hp
  simp only [marketInitcodeMemory, marketInitcodeCopyMemory, writeWord_sparse_size]
  rw [copyZeroMemory_size _ _ _ _ _ (by dsimp only [MarketData.encodingSize]; omega)
    (by rw [hf]; omega)]
  omega

theorem marketInitcodeMemory_bytes (mem : ByteArray) {root prefixPtr encoded : UInt256}
    (m : MarketData) (hroot : 96 ≤ root.toNat) (hsmall : 11 + m.encodingSize < 2^64)
    (hp : prefixPtr.toNat + 43 ≤ mem.size)
    (he : encoded.toNat + 32 + m.encodingSize ≤ mem.size)
    (hbefore : encoded.toNat + 32 + m.encodingSize ≤ root.toNat + 32)
    (hprefix : mem.readWithPadding (prefixPtr.toNat + 32) 11 = Model.sstore2Prefix)
    (hencoded : mem.readWithPadding (encoded.toNat + 32) m.encodingSize =
      wordArrayBytes m.encodedWords) :
    (marketInitcodeMemory mem root prefixPtr encoded m).readWithPadding
      (root.toNat + 32) (11 + m.encodingSize) = m.initcode := by
  have hpos : 0 < m.encodingSize := by dsimp only [MarketData.encodingSize]; omega
  have hf := marketInitcodeFirstMemory_size mem root prefixPtr hp
  have hefirst : (encoded.toNat + 32) + m.encodingSize ≤
      (marketInitcodeFirstMemory mem root prefixPtr).size := by rw [hf]; omega
  have hc : root.toNat + 43 + m.encodingSize + 32 ≤
      (marketInitcodeCopyMemory mem root prefixPtr encoded m).size := by
    rw [marketInitcodeCopyMemory, copyZeroMemory_size _ _ _ _ _ (by omega) hefirst]
    omega
  have hhead : (marketInitcodeCopyMemory mem root prefixPtr encoded m).readWithPadding
      (root.toNat + 32) 11 = Model.sstore2Prefix := by
    rw [marketInitcodeCopyMemory, copyZeroMemory_read_before _ _ _ _ _ _ _ (by omega)
      hefirst (by decide) (by decide) (by rw [hf]; omega) (by omega),
      marketInitcodeFirstMemory, copyZeroMemory_read _ _ _ _ _ (by decide) (by omega) (by decide),
      hprefix]
  have htail : (marketInitcodeCopyMemory mem root prefixPtr encoded m).readWithPadding
      (root.toNat + 43) m.encodingSize = wordArrayBytes m.encodedWords := by
    rw [marketInitcodeCopyMemory, copyZeroMemory_read _ _ _ _ _ hpos hefirst (by omega),
      marketInitcodeFirstMemory, copyZeroMemory_read_before _ _ _ _ _ _ _ (by decide)
      (by omega) hpos (by omega) he hbefore, hencoded]
  rw [marketInitcodeMemory, writeWord_sparse_read_preserved_len _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (Or.inr (by omega)) (by omega) (by omega),
    writeWord_sparse_read_preserved_len _ _ _ _ _ (by omega) (Or.inr le_rfl) (by omega) (by omega)]
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) hpos (by omega), hhead]
  simp only [Nat.add_assoc, Nat.reduceAdd, htail, MarketData.initcode]

end Benchmarks.Midnight
