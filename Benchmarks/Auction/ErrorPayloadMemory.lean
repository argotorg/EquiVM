import Benchmarks.Auction.CopyMemory
import Benchmarks.Auction.ReturnReserve

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def errorOffset (out : ByteArray) : UInt256 := calldataWord out 4
def errorLength (out : ByteArray) : UInt256 := calldataWord out (4 + (errorOffset out).toNat)

noncomputable def errorPayloadMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  out.write 4 mem ptr.toNat (out.size - 4)

def errorPayloadWords (aw ptr : UInt256) (out : ByteArray) : UInt256 :=
  expandedWords aw ptr (UInt256.ofNat (out.size - 4))

-- LIBRARY CANDIDATE: a symbolic expansion covers the complete requested memory interval.
theorem expandedWords_cover {aw off size : UInt256} (ha : ActiveWords aw)
    (hb : off.toNat + size.toNat ≤ 2 ^ 200) (hz : size.toNat ≠ 0) :
    off.toNat + size.toNat ≤ (expandedWords aw off size).toNat * 32 := by
  have hm := memoryWords_bounds aw.toNat off.toNat size.toNat ha.2 hb
  have hn : (expandedWords aw off size).toNat =
      MachineState.M aw.toNat off.toNat size.toNat := by
    apply ulit_toNat'
    change _ < 2 ^ 256
    omega
  rw [hn]
  unfold MachineState.M
  cases hs : size.toNat with
  | zero => exact False.elim (hz hs)
  | succ n =>
    change off.toNat + (n + 1) ≤ max aw.toNat ((off.toNat + (n + 1) + 31) / 32) * 32
    omega

theorem errorPayload_size {mem aw ptr out} (_hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size) :
    (errorPayloadMem mem out ptr).size = max mem.size (ptr.toNat + out.size - 4) := by
  have hs := copyWindow_size out mem 4 ptr.toNat (out.size - 4) (by omega) (by omega) hin
  simpa only [errorPayloadMem, Nat.add_sub_assoc (show 4 ≤ out.size by omega)] using hs

theorem errorPayloadHeap {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) :
    HeapMemory (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) ptr := by
  have hn : (UInt256.ofNat (out.size - 4)).toNat = out.size - 4 :=
    ulit_toNat' _ (by change out.size - 4 < 2 ^ 256; omega)
  have hsz := errorPayload_size hm hin hl
  refine ⟨by have hs := hm.size; omega, ?_, hm.lower, by have hg := hm.gap; omega, ?_⟩
  · rw [errorPayloadMem, copyWindow_read_preserved out mem 4 ptr.toNat (out.size - 4) 64
      (by omega) (by omega) hin hm.size (Or.inl (by have hp := hm.lower; omega)), hm.free]
  · apply activeWords_expand hm.active
    rw [hn]
    omega

theorem errorPayloadCover {aw ptr out} (ha : ActiveWords aw) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) :
    ptr.toNat + out.size - 4 ≤ (errorPayloadWords aw ptr out).toNat * 32 := by
  have hn : (UInt256.ofNat (out.size - 4)).toNat = out.size - 4 :=
    ulit_toNat' _ (by change out.size - 4 < 2 ^ 256; omega)
  have hc := expandedWords_cover (off := ptr) (size := UInt256.ofNat (out.size - 4)) ha
    (by rw [hn]; omega) (by rw [hn]; omega)
  simpa only [errorPayloadWords, hn, Nat.add_sub_assoc (show 4 ≤ out.size by omega)] using hc

theorem errorPayload_load {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (off : UInt256)
    (hoff : off.toNat + 36 ≤ out.size) :
    loadedWord (errorPayloadMem mem out ptr) (errorPayloadWords aw ptr out) (ptr + off) =
      calldataWord out (4 + off.toNat) := by
  have hp : (ptr + off).toNat = ptr.toNat + off.toNat :=
    addWord_toNat ptr off (by change ptr.toNat + off.toNat < 2 ^ 256; omega)
  have hsz := errorPayload_size hm hin hl
  have hc := errorPayloadCover hm.active hl hb
  have hh := errorPayloadHeap hm hin hl hb
  apply loadedWord_of_read hh.active (by omega) (by omega)
  rw [hp, errorPayloadMem, copyWindow_read_word out mem 4 ptr.toNat (out.size - 4) off.toNat
      (by omega) (by omega) hin (by omega),
    readWithPadding_eq_extract _ _ (by omega), calldataWord_bytes_at (by omega)]

theorem errorPayload_expand {mem aw ptr out} (hm : HeapMemory mem aw ptr)
    (hin : ptr.toNat ≤ mem.size) (hl : 68 ≤ out.size)
    (hb : ptr.toNat + out.size ≤ 2 ^ 200) (off : UInt256)
    (hoff : off.toNat + 36 ≤ out.size) :
    expandedWords (errorPayloadWords aw ptr out) (ptr + off) ⟨32⟩ =
      errorPayloadWords aw ptr out := by
  have hp : (ptr + off).toNat = ptr.toNat + off.toNat :=
    addWord_toNat ptr off (by change ptr.toNat + off.toNat < 2 ^ 256; omega)
  have hc := errorPayloadCover hm.active hl hb
  have hh := errorPayloadHeap hm hin hl hb
  exact expandedWords32_eq_of_cover hh.active (by omega) (by omega)

end Auction
