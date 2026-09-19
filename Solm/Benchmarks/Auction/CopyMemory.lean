import Solm.Benchmarks.Auction.CallOutput
import Solm.Benchmarks.Auction.BytesMemory
import Solm.Benchmarks.Auction.MemoryGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- GENERALIZES Reasoning.Theory.write_eq_gen_from to a copy that can extend memory.
theorem copyWindow_eq (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    src.write srcOff mem dest len = mem.extract 0 dest ++ src.extract srcOff (srcOff + len) ++
      mem.extract (dest + len) mem.size := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hpos, if_neg (show ¬ srcOff ≥ src.size by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - srcOff) = len := by omega
  have hsp : min mem.size (dest + len) - (dest + len) = 0 :=
    Nat.sub_eq_zero_of_le (Nat.min_le_right _ _)
  have hdp : dest - mem.size = 0 := Nat.sub_eq_zero_of_le hdest
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl, Array.append_empty,
    hsize, hpL, hsp, Nat.add_zero, show mem.data.size = mem.size from rfl]

theorem copyWindow_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest + len) := by
  rw [copyWindow_eq src mem srcOff dest len hpos hsrc hdest]
  simp only [ByteArray.size_append, ByteArray.size_extract]
  omega

theorem copyWindow_extract (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hwithin : off + count ≤ len) :
    (src.write srcOff mem dest len).extract (dest + off) (dest + off + count) =
      src.extract (srcOff + off) (srcOff + off + count) := by
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [copyWindow_eq src mem srcOff dest len hpos hsrc hdest,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
    extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp]
  rw [show dest + off - dest = off by omega,
    show dest + off + count - dest = off + count by omega, extract_extract_BA]
  congr 1
  omega

theorem copyWindow_read_word (src mem : ByteArray) (srcOff dest len off : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hwithin : off + 32 ≤ len) :
    (src.write srcOff mem dest len).readWithPadding (dest + off) 32 =
      src.readWithPadding (srcOff + off) 32 := by
  rw [readWithPadding_eq_extract _ _ (by
      rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]; omega),
    readWithPadding_eq_extract _ _ (by omega),
    copyWindow_extract src mem srcOff dest len off 32 hpos hsrc hdest hwithin]

theorem copyWindow_read_preserved (src mem : ByteArray) (srcOff dest len read : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hin : read + 32 ≤ mem.size) (hdisj : read + 32 ≤ dest ∨ dest + len ≤ read) :
    (src.write srcOff mem dest len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract _ _ (by
      rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]; omega),
    readWithPadding_eq_extract _ _ hin, copyWindow_eq src mem srcOff dest len hpos hsrc hdest]
  rcases hdisj with hlo | hhi
  · rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
      extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
    congr 1 <;> omega
  · rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
      ByteArray.size_append, hp, hs, extract_extract_BA]
    congr 1 <;> omega

theorem copyWindow_prefix (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hdisj : limit ≤ dest ∨ dest + len ≤ 96) :
    MemoryPrefix mem (src.write srcOff mem dest len) limit := by
  refine ⟨?_, fun read hlo hhi hin ↦ ?_⟩
  · rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]
    exact Nat.le_max_left _ _
  · exact copyWindow_read_preserved src mem srcOff dest len read hpos hsrc hdest hin
      (hdisj.elim (fun hd ↦ Or.inl (by omega)) (fun hd ↦ Or.inr (by omega)))

theorem loadedWord_zero {mem aw} (ha : ActiveWords aw) (hm : 32 ≤ mem.size) :
    loadedWord mem aw ⟨0⟩ = calldataWord mem 0 := by
  apply loadedWord_of_read (off := ⟨0⟩) ha (by change 0 + 32 ≤ mem.size; omega)
    (by have hlo := ha.1; change 0 < _; omega)
  change mem.readWithPadding 0 32 = _
  rw [readWithPadding_eq_extract _ _ hm, calldataWord_bytes hm]

end Auction
