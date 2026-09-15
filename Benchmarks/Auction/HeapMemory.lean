import Benchmarks.Auction.DynamicMemory
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the allocated prefix survives writes to the free-memory area.
structure MemoryPrefix (before after : ByteArray) (limit : Nat) : Prop where
  size : before.size ≤ after.size
  read : ∀ off, 96 ≤ off → off + 32 ≤ limit → off + 32 ≤ before.size →
    after.readWithPadding off 32 = before.readWithPadding off 32

theorem MemoryPrefix.refl (mem : ByteArray) (limit : Nat) : MemoryPrefix mem mem limit :=
  ⟨le_refl _, fun _ _ _ _ => rfl⟩

theorem MemoryPrefix.trans {a b c : ByteArray} {limit : Nat}
    (hab : MemoryPrefix a b limit) (hbc : MemoryPrefix b c limit) :
    MemoryPrefix a c limit := by
  refine ⟨le_trans hab.size hbc.size, fun off hlo hhi hin => ?_⟩
  rw [hbc.read off hlo hhi (le_trans hin hab.size), hab.read off hlo hhi hin]

theorem MemoryPrefix.mono {a b : ByteArray} {lo hi : Nat}
    (h : MemoryPrefix a b hi) (hle : lo ≤ hi) : MemoryPrefix a b lo :=
  ⟨h.size, fun off hlo hhi hin => h.read off hlo (le_trans hhi hle) hin⟩

theorem memoryPrefix_writeWord (mem : ByteArray) (off limit : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) (hdisj : limit ≤ off ∨ off + 32 ≤ 96) :
    MemoryPrefix mem (writeWord mem off word) limit := by
  refine ⟨?_, fun read hlo hhi hin => ?_⟩
  · rw [writeWord_size mem off word hgap]
    exact Nat.le_max_left _ _
  · apply writeWord_read_preserved mem off read word hgap
    rcases hdisj with hb | ha
    · exact Or.inl ⟨le_trans hhi hb, hin⟩
    · exact Or.inr ⟨le_trans ha hlo, hin⟩

def ActiveWords (aw : UInt256) : Prop := 3 ≤ aw.toNat ∧ aw.toNat ≤ 2 ^ 200

structure HeapMemory (mem : ByteArray) (aw ptr : UInt256) : Prop where
  size : 96 ≤ mem.size
  free : mem.readWithPadding 64 32 = ptr.toByteArray
  lower : 128 ≤ ptr.toNat
  gap : ptr.toNat ≤ mem.size + 32
  active : ActiveWords aw

theorem addWord_toNat (a b : UInt256) (h : a.toNat + b.toNat < UInt256.size) :
    (UInt256.add a b).toNat = a.toNat + b.toNat := by
  change (a.toNat + b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt h

theorem activeWords_mul32 {aw : UInt256} (h : ActiveWords aw) :
    (aw * ⟨32⟩).toNat = aw.toNat * 32 := by
  change (aw.toNat * 32) % UInt256.size = _
  apply Nat.mod_eq_of_lt
  have hb := h.2
  change aw.toNat * 32 < 2 ^ 256
  omega

theorem loadedWord_of_read {mem : ByteArray} {aw off word : UInt256}
    (hactive : ActiveWords aw) (hmem : off.toNat + 32 ≤ mem.size)
    (hcover : off.toNat < aw.toNat * 32)
    (hread : mem.readWithPadding off.toNat 32 = word.toByteArray) :
    loadedWord mem aw off = word := by
  apply mloadWordValue_of_readWithPadding (by omega) _ hread
  change ¬ (aw * ⟨32⟩).toNat ≤ off.toNat
  rw [activeWords_mul32 hactive]
  omega

theorem expandedWords32_toNat {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) :
    (expandedWords aw off ⟨32⟩).toNat = max aw.toNat ((off.toNat + 63) / 32) := by
  change max aw.toNat ((off.toNat + 32 + 31) / 32) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by
    have hb := ha.2
    change max aw.toNat ((off.toNat + 32 + 31) / 32) < 2 ^ 256
    omega)]

theorem activeWords_expand32 {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) : ActiveWords (expandedWords aw off ⟨32⟩) := by
  unfold ActiveWords
  rw [expandedWords32_toNat ha hoff]
  have hlo := ha.1
  have hhi := ha.2
  constructor <;> omega

theorem expandedWords32_cover {aw off : UInt256} (ha : ActiveWords aw)
    (hoff : off.toNat + 32 ≤ 2 ^ 200) :
    off.toNat < (expandedWords aw off ⟨32⟩).toNat * 32 := by
  rw [expandedWords32_toNat ha hoff]
  omega

theorem expandedWords64_eq {aw : UInt256} (ha : ActiveWords aw) :
    expandedWords aw ⟨64⟩ ⟨32⟩ = aw := by
  apply u256_inj
  rw [expandedWords32_toNat ha (by decide)]
  have hlo := ha.1
  change max aw.toNat 3 = aw.toNat
  exact max_eq_left hlo

theorem HeapMemory.load64 {mem aw ptr} (h : HeapMemory mem aw ptr) :
    loadedWord mem aw ⟨64⟩ = ptr := by
  exact loadedWord_of_read h.active h.size (by have hlo := h.active.1; change 64 < _; omega)
    h.free

theorem HeapMemory.writeAbove {mem aw ptr} (h : HeapMemory mem aw ptr)
    (off word : UInt256) (hlo : ptr.toNat ≤ off.toNat)
    (hgap : off.toNat ≤ mem.size + 32) (hbound : off.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (writeWord mem off.toNat word) (expandedWords aw off ⟨32⟩) ptr := by
  have hg : off.toNat - mem.size < USize.size := by
    have h32 : 32 < USize.size := lt_usize 32 (by decide)
    omega
  have hs := writeWord_size mem off.toNat word hg
  refine ⟨by have hm := h.size; omega, ?_, h.lower, ?_,
    activeWords_expand32 h.active hbound⟩
  · rw [writeWord_read_preserved mem off.toNat 64 word hg (Or.inl
      ⟨by have hp := h.lower; omega, h.size⟩), h.free]
  · have hp := h.gap
    omega

theorem HeapMemory.setFree {mem aw ptr} (h : HeapMemory mem aw ptr) (next : UInt256)
    (hlo : 128 ≤ next.toNat) (hgap : next.toNat ≤ mem.size + 32) :
    HeapMemory (writeWord mem 64 next) aw next := by
  have hg : 64 - mem.size < USize.size := by
    have hm := h.size
    have hz : 0 < USize.size := lt_usize 0 (by decide)
    omega
  have hs := writeWord_size mem 64 next hg
  refine ⟨by have hm := h.size; omega, writeWord_read_back mem 64 next hg,
    hlo, ?_, h.active⟩
  omega

theorem freshHeapMemory : HeapMemory solcFreePtrMem ⟨3⟩ ⟨128⟩ := by
  exact ⟨by rw [solcFreePtrMem_size], solcFreePtrMem_read64, by decide,
    by rw [solcFreePtrMem_size]; decide, by constructor <;> decide⟩

end Auction
