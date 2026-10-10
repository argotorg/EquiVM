import Benchmarks.CompoundIII.Comet.AssetDecode
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: transferring a word load across a preserved memory prefix.
theorem memoryPrefix_load {before after : ByteArray} {limit : Nat} {ptr : UInt256}
    (hp : MemoryPrefix before after limit) (hlo : 96 ≤ ptr.toNat)
    (hlim : ptr.toNat + 32 ≤ limit) (hin : ptr.toNat + 32 ≤ before.size) :
    memLoad ptr after = memLoad ptr before := by
  have hs := hp.size
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega), hp.read _ hlo hlim hin]

def assetStore (mem : ByteArray) (dest : UInt256) (out : ByteArray) (n : Nat) : ByteArray :=
  writeCascade mem ((List.range n).map fun j ↦
    ((dest + UInt256.ofNat (32 * j)).toNat, calldataWord out (32 * j)))

theorem assetStore_zero (mem : ByteArray) (dest : UInt256) (out : ByteArray) :
    assetStore mem dest out 0 = mem := rfl

theorem assetStore_succ (mem : ByteArray) (dest : UInt256) (out : ByteArray) (n : Nat) :
    assetStore mem dest out (n + 1) = writeWord (assetStore mem dest out n)
      (dest + UInt256.ofNat (32 * n)).toNat (calldataWord out (32 * n)) := by
  simp only [assetStore, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    writeCascade_append, writeCascade_cons, writeCascade_nil]

theorem assetStore_one (mem : ByteArray) (dest : UInt256) (out : ByteArray) :
    assetStore mem dest out 1 = writeWord mem dest.toNat (calldataWord out 0) := by
  rw [assetStore_succ, assetStore_zero]
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    uint256_add_zero_right]

theorem assetStore_prefix {mem out : ByteArray} {dest : UInt256} {n limit : Nat}
    (hn : n ≤ 8) (hb : dest.toNat + 256 < UInt256.size) (hl : limit ≤ dest.toNat) :
    MemoryPrefix mem (assetStore mem dest out n) limit := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
  have hj' := List.mem_range.mp hj
  left
  dsimp only
  rw [uadd_word_ofNat_toNat _ _ (by omega)]
  omega

theorem assetStore_size {mem out : ByteArray} {dest : UInt256} {n : Nat}
    (hn : n ≤ 8) (hpos : 0 < n) (hb : dest.toNat + 256 < UInt256.size) :
    (assetStore mem dest out n).size = max mem.size (dest.toNat + 32 * n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [assetStore_succ, writeWord_sparse_size, uadd_word_ofNat_toNat _ _ (by omega)]
      cases n with
      | zero => simp [assetStore_zero]
      | succ n => rw [ih (by omega) (by omega)]; omega

theorem assetStore_word {mem out : ByteArray} {dest : UInt256} {n j : Nat}
    (hn : n ≤ 8) (hj : j < n) (hb : dest.toNat + 256 < UInt256.size) :
    memLoad (dest + UInt256.ofNat (32 * j)) (assetStore mem dest out n) =
      calldataWord out (32 * j) := by
  have haddr : (dest + UInt256.ofNat (32 * j)).toNat = dest.toNat + 32 * j :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hread : (assetStore mem dest out n).readWithPadding (dest.toNat + 32 * j) 32 =
      (calldataWord out (32 * j)).toByteArray := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [assetStore_succ, uadd_word_ofNat_toNat _ _ (by omega)]
        by_cases he : j = n
        · subst j
          exact writeWord_sparse_read_back _ _ _
        · have hjn : j < n := by omega
          rw [writeWord_sparse_read_preserved _ _ _ _
            (Or.inl ⟨by omega, by rw [assetStore_size (by omega) (by omega) hb]; omega⟩)]
          exact ih (by omega) hjn
  apply loadedWord_of_read
  · rw [haddr, assetStore_size hn (by omega) hb]; omega
  · rw [haddr]; exact hread

-- LIBRARY CANDIDATE: reconstructing a contiguous buffer from its word-sized reads.
theorem readWordBlock (mem : ByteArray) (start n : Nat) (words : Nat → UInt256)
    (hpos : 0 < n) (hin : start + 32 * n ≤ mem.size)
    (hr : ∀ j < n, mem.readWithPadding (start + 32 * j) 32 = (words j).toByteArray) :
    mem.readWithPadding start (32 * n) = wordBytes ((List.range n).map words) := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
            List.map_nil, wordBytes, ByteArray.append_empty, Nat.mul_one,
            Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
      | succ n =>
          rw [Nat.mul_succ, byteArray_readWithPadding_split_unbounded _ _ _ _
            (by omega) (by decide) (by omega),
            ih (by omega) (by omega) (fun j hj ↦ hr j (by omega)), hr _ (by omega),
            List.range_succ (n := n + 1), List.map_append, wordBytes_append]
          simp only [List.map_cons, List.map_nil, wordBytes, ByteArray.append_empty]

theorem assetStore_read {mem out : ByteArray} {dest : UInt256} {n : Nat}
    (hn : n ≤ 8) (hpos : 0 < n) (hb : dest.toNat + 256 < UInt256.size) :
    (assetStore mem dest out n).readWithPadding dest.toNat (32 * n) =
      wordBytes ((List.range n).map fun j ↦ calldataWord out (32 * j)) := by
  apply readWordBlock _ _ _ _ hpos
  · rw [assetStore_size hn hpos hb]; omega
  · intro j hj
    have ha := uadd_word_ofNat_toNat dest (32 * j) (by omega)
    have hm := assetStore_word (mem := mem) (out := out) hn hj hb
    have hs : (dest + UInt256.ofNat (32 * j)).toNat + 32 ≤
        (assetStore mem dest out n).size := by
      rw [ha, assetStore_size hn hpos hb]; omega
    unfold memLoad at hm
    rw [if_neg (by omega)] at hm
    have hr := congrArg UInt256.toByteArray hm
    rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size (by
      rw [readWithPadding_eq_extract _ _ hs, ByteArray.size_extract]; omega)] at hr
    rw [ha] at hr
    exact hr

end Benchmarks.CompoundIII.Comet
