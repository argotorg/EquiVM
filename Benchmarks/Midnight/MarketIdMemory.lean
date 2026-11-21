import Benchmarks.Midnight.MarketIdSource
import Benchmarks.Midnight.PackedAddressBytes
import Benchmarks.Midnight.MemoryPrefix

/-! The 85-byte CREATE2 hash preimage constructed by the Midnight runtime. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketIdPayload (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  writeWordArray (writeWord (writeWord mem (root.toNat + 32)
    (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 248))) (root.toNat + 33)
    (UInt256.shiftLeft (UInt256.ofNat m.midnight.val) (UInt256.ofNat 96))) (root.toNat + 53)
    [⟨0⟩, uInt256OfByteArray (KEC m.initcode)]

def marketIdMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  writeWord (writeWord (marketIdPayload mem root m) root.toNat (UInt256.ofNat 85))
    64 (root + UInt256.ofNat 128)

theorem marketIdPayload_size (mem : ByteArray) (root : UInt256) (m : MarketData) :
    (marketIdPayload mem root m).size = max mem.size (root.toNat + 117) := by
  simp only [marketIdPayload, writeWordArray, writeWord_sparse_size]
  omega

theorem marketIdPayload_bytes (mem : ByteArray) (root : UInt256) (m : MarketData) :
    (marketIdPayload mem root m).readWithPadding (root.toNat + 32) 85 = m.idPreimage := by
  let ff := UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 248)
  let addr := UInt256.shiftLeft (UInt256.ofNat m.midnight.val) (UInt256.ofNat 96)
  let first := writeWord mem (root.toNat + 32) ff
  let second := writeWord first (root.toNat + 33) addr
  have hfirst : root.toNat + 64 ≤ first.size := by
    dsimp only [first]; rw [writeWord_sparse_size]; omega
  have hsecond : root.toNat + 65 ≤ second.size := by
    dsimp only [second]; rw [writeWord_sparse_size]; omega
  have h1 : (marketIdPayload mem root m).readWithPadding (root.toNat + 32) 1 =
      ff.toByteArray.extract 0 1 := by
    rw [marketIdPayload, writeWordArray_read_below_len _ _ _ _ _ (by exact le_trans (by omega) hsecond)
      (by omega) (by decide) (by decide)]
    change (Reasoning.Theory.writeWord first (root.toNat + 33) addr).readWithPadding
      (root.toNat + 32) 1 = _
    rw [writeWord_sparse_read_preserved_len _ _ _ _ _ (by omega) (Or.inl (by omega))
      (by decide) (by decide)]
    exact writeWord_sparse_read_window mem (root.toNat + 32) 0 1 ff
      (by decide) (by decide) (by decide)
  have h20 : (marketIdPayload mem root m).readWithPadding (root.toNat + 33) 20 =
      addr.toByteArray.extract 0 20 := by
    rw [marketIdPayload, writeWordArray_read_below_len _ _ _ _ _
      (by exact le_trans (by omega) hsecond) (by omega) (by decide) (by decide)]
    exact writeWord_sparse_read_window first (root.toNat + 33) 0 20 addr
      (by decide) (by decide) (by decide)
  have h64 : (marketIdPayload mem root m).readWithPadding (root.toNat + 53) 64 =
      (⟨0⟩ : UInt256).toByteArray ++ (uInt256OfByteArray (KEC m.initcode)).toByteArray := by
    have hr := writeWordArray_read second (root.toNat + 53)
      [⟨0⟩, uInt256OfByteArray (KEC m.initcode)] (by omega)
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      wordArrayBytes, ByteArray.append_empty] using hr
  have hs := marketIdPayload_size mem root m
  rw [show 85 = 1 + (20 + 64) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [hs]; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [byteArray_readWithPadding_split_unbounded _ _ 20 64 (by decide) (by decide)
    (by rw [hs]; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd, h1, h20, h64]
  have hff : ff.toByteArray.extract 0 1 = ⟨#[255]⟩ := by decide +kernel
  rw [hff, toByteArray_uInt256OfByteArray_of_size32 (keccak_size m.initcode)]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← byteArray_toList_eq, ← byteArray_toList_eq]
  have haddr : (addr.toByteArray.extract 0 20).toList =
      (EVM.word m.midnight.val).toBytesBE.drop 12 := packedAddressBytes m.midnight
  simp only [byteArray_toList_append, haddr,
    ← word_toBytesBE_eq_toByteArray_toList]
  simp [MarketData.idPreimage, byteArray_toList_eq, List.append_assoc,
    show (⟨0⟩ : UInt256) = UInt256.ofNat 0 from rfl]

theorem marketIdMemory_prefix (mem : ByteArray) (root : UInt256) (m : MarketData) :
    MemoryPrefix mem (marketIdMemory mem root m) root.toNat := by
  exact ((((memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl))).trans
    (memoryPrefix_writeWord _ 64 _ _ (Or.inr (by decide)))

theorem marketIdMemory_free (mem : ByteArray) (root : UInt256) (m : MarketData) :
    memLoad (UInt256.ofNat 64) (marketIdMemory mem root m) = root + UInt256.ofNat 128 :=
  memLoad_writeWord _ _ _

theorem marketIdMemory_length (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat) : memLoad root (marketIdMemory mem root m) = UInt256.ofNat 85 := by
  rw [marketIdMemory, memLoad_writeWord_preserved]
  · exact memLoad_writeWord _ _ _
  · rw [writeWord_sparse_size]; omega
  · right; change 64 + 32 ≤ root.toNat; exact hroot

theorem marketIdMemory_bytes (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat) :
    (marketIdMemory mem root m).readWithPadding (root.toNat + 32) 85 = m.idPreimage := by
  have hs := marketIdPayload_size mem root m
  rw [marketIdMemory, writeWord_sparse_read_preserved_len _ _ _ _ _
    (by rw [writeWord_sparse_size, hs]; omega) (Or.inr (by omega)) (by decide) (by decide),
    writeWord_sparse_read_preserved_len _ _ _ _ _ (by rw [hs]; omega) (Or.inr le_rfl)
    (by decide) (by decide), marketIdPayload_bytes]

theorem marketIdMemory_hash (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hroot : 96 ≤ root.toNat) (hbound : root.toNat + 32 < UInt256.size) :
    keccakWord (root + UInt256.ofNat 32) (UInt256.ofNat 85) (marketIdMemory mem root m) = m.id := by
  rw [keccakWord, uadd_word_ofNat_toNat _ _ hbound]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((marketIdMemory mem root m).readWithPadding (root.toNat + 32) 85))) = _
  rw [marketIdMemory_bytes mem m hroot]
  exact (uInt256OfByteArray_eq _).symm

end Benchmarks.Midnight
