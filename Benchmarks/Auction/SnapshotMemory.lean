import Benchmarks.Auction.Snapshot
import Benchmarks.Auction.SparseMemory
import Benchmarks.Auction.MemoryGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

noncomputable def Snapshot.mem (s : Snapshot) (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeCascade (writeWord mem 64 (ptr + ⟨192⟩))
    [(ptr.toNat, s.nounId), (ptr.toNat + 32, s.amount), (ptr.toNat + 64, s.startTime),
      (ptr.toNat + 96, s.endTime), (ptr.toNat + 128, s.bidderWord), (ptr.toNat + 160,
        s.settledWord)]

def snapshotWords (aw ptr : UInt256) : UInt256 := expandedWords aw (ptr + ⟨160⟩) ⟨32⟩

theorem Snapshot.mem_size (s : Snapshot) {mem : ByteArray} {ptr : UInt256} (hm : 96 ≤ mem.size)
    (hp : 128 ≤ ptr.toNat) : (s.mem mem ptr).size = max mem.size (ptr.toNat + 192) := by
  simp only [Snapshot.mem, writeCascade, writeWord_sparse_size]
  omega

theorem Snapshot.mem_free (s : Snapshot) {mem : ByteArray} {ptr : UInt256} (_hm : 96 ≤ mem.size)
    (hp : 128 ≤ ptr.toNat) : (s.mem mem ptr).readWithPadding 64 32 = (ptr + ⟨192⟩).toByteArray := by
  simp only [Snapshot.mem, writeCascade]
  repeat' first
    | rw [writeWord_sparse_read_back]
    | refine Eq.trans (writeWord_sparse_read_preserved _ _ _ _ ?_) ?_
      · left
        constructor <;> (try simp only [writeWord_sparse_size]) <;> omega

theorem sparseCascade_read_below (mem : ByteArray) (writes : List (Nat × UInt256)) (read : Nat)
    (hin : read + 32 ≤ mem.size) (hbelow : ∀ w ∈ writes, read + 32 ≤ w.1) :
    (writeCascade mem writes).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction writes generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [writeCascade_cons]
    have hin' : read + 32 ≤ (writeWord mem w.1 w.2).size := by
      rw [writeWord_sparse_size]
      exact le_trans hin (Nat.le_max_left _ _)
    rw [ih (writeWord mem w.1 w.2) hin' (fun w hw ↦ hbelow w (List.mem_cons_of_mem _ hw))]
    exact writeWord_sparse_read_preserved mem w.1 read w.2
      (Or.inl ⟨hbelow w List.mem_cons_self, hin⟩)

theorem sparseCascade_read_word (mem : ByteArray) (off : Nat) (word : UInt256)
    (rest : List (Nat × UInt256)) (hlater : ∀ w ∈ rest, off + 32 ≤ w.1) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding off 32 = word.toByteArray := by
  rw [writeCascade_cons, sparseCascade_read_below _ rest off
    (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _) hlater]
  exact writeWord_sparse_read_back _ _ _

theorem Snapshot.mem_read (s : Snapshot) (mem : ByteArray) (ptr : UInt256) (i : Fin 6) :
    (s.mem mem ptr).readWithPadding (ptr.toNat + 32 * i.val) 32 =
      s.words[i.val].toByteArray := by
  fin_cases i <;> norm_num only [Snapshot.mem, Snapshot.words, List.getElem_cons,
    List.getElem_zero, List.head_cons]
  all_goals simp only [dif_neg (show ¬False from id), Nat.add_zero]
  case «0» =>
    apply sparseCascade_read_word
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega
  case «1» =>
    rw [writeCascade_cons]
    apply sparseCascade_read_word
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> omega
  case «2» =>
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    apply sparseCascade_read_word
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> omega
  case «3» =>
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    apply sparseCascade_read_word
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega
  case «4» =>
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    apply sparseCascade_read_word
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl
    omega
  case «5» =>
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    rw [writeCascade_cons]
    apply sparseCascade_read_word
    intro w hw
    simp at hw

theorem memoryPrefix_sparse_cascade (mem : ByteArray) (writes : List (Nat × UInt256)) (limit : Nat)
    (hdisj : ∀ write ∈ writes, limit ≤ write.1 ∨ write.1 + 32 ≤ 96) :
    MemoryPrefix mem (writeCascade mem writes) limit := by
  induction writes generalizing mem with
  | nil => exact .refl _ _
  | cons w ws ih =>
    exact (memoryPrefix_sparse_writeWord mem w.1 limit w.2 (hdisj w (by simp))).trans
      (ih _ (fun w hw ↦ hdisj w (List.mem_cons_of_mem _ hw)))

theorem Snapshot.mem_prefix (s : Snapshot) (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (s.mem mem ptr) ptr.toNat := by
  unfold Snapshot.mem
  apply MemoryPrefix.trans
    (memoryPrefix_sparse_writeWord mem 64 ptr.toNat (ptr + ⟨192⟩) (Or.inr (by decide)))
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl (by omega)

theorem Snapshot.mem_cursorHeap (s : Snapshot) {mem aw ptr} (hm : MemoryCursor mem aw ptr)
    (hb : ptr.toNat + 192 ≤ 2 ^ 200) :
    HeapMemory (s.mem mem ptr) (snapshotWords aw ptr) (ptr + ⟨192⟩) := by
  have hp : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
    addWord_toNat ptr ⟨192⟩ (by change ptr.toNat + 192 < 2 ^ 256; omega)
  have h160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 :=
    addWord_toNat ptr ⟨160⟩ (by change ptr.toNat + 160 < 2 ^ 256; omega)
  have hsz := s.mem_size hm.size hm.lower
  refine ⟨by omega, s.mem_free hm.size hm.lower, by have hlo := hm.lower; omega, by omega, ?_⟩
  exact activeWords_expand32 hm.active (by omega)

theorem Snapshot.mem_heap (s : Snapshot) {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 192 ≤ 2 ^ 200) :
    HeapMemory (s.mem mem ptr) (snapshotWords aw ptr) (ptr + ⟨192⟩) :=
  s.mem_cursorHeap hm.cursor hb

structure SnapshotMemory (s : Snapshot) (mem : ByteArray) (aw ptr : UInt256) : Prop where
  lower : 96 ≤ ptr.toNat
  bound : ptr.toNat + 192 ≤ 2 ^ 200
  size : ptr.toNat + 192 ≤ mem.size
  active : ActiveWords aw
  cover : ptr.toNat + 192 ≤ aw.toNat * 32
  read : ∀ i : Fin 6, mem.readWithPadding (ptr.toNat + 32 * i.val) 32 = s.words[i.val].toByteArray

theorem snapshotMemory_cursorMade (s : Snapshot) {mem aw ptr} (hm : MemoryCursor mem aw ptr)
    (hb : ptr.toNat + 192 ≤ 2 ^ 200) : SnapshotMemory s (s.mem mem ptr) (snapshotWords aw ptr)
      ptr := by
  have h160 : (ptr + ⟨160⟩).toNat = ptr.toNat + 160 :=
    addWord_toNat ptr ⟨160⟩ (by change ptr.toNat + 160 < 2 ^ 256; omega)
  have hh := s.mem_cursorHeap hm hb
  refine ⟨by have hlo := hm.lower; omega, hb,
    by rw [s.mem_size hm.size hm.lower]; exact Nat.le_max_right _ _, hh.active, ?_, s.mem_read _ _⟩
  unfold snapshotWords
  rw [expandedWords32_toNat hm.active (by omega), h160]
  omega

theorem snapshotMemory_made (s : Snapshot) {mem aw ptr} (hm : HeapMemory mem aw ptr)
    (hb : ptr.toNat + 192 ≤ 2 ^ 200) : SnapshotMemory s (s.mem mem ptr) (snapshotWords aw ptr)
      ptr :=
  snapshotMemory_cursorMade s hm.cursor hb

theorem SnapshotMemory.transport {s mem mem' aw aw' ptr limit}
    (h : SnapshotMemory s mem aw ptr) (hp : MemoryPrefix mem mem' limit)
    (hl : ptr.toNat + 192 ≤ limit) (ha : ActiveWords aw') (hm : aw.toNat ≤ aw'.toNat) :
    SnapshotMemory s mem' aw' ptr := by
  refine ⟨h.lower, h.bound, le_trans h.size hp.size, ha, by have hc := h.cover; omega, ?_⟩
  intro i
  have hi := i.isLt
  rw [hp.read (ptr.toNat + 32 * i.val) (by have hlo := h.lower; omega) (by omega)
    (by have hs := h.size; omega), h.read i]

theorem SnapshotMemory.load {s mem aw ptr} (h : SnapshotMemory s mem aw ptr) (i : Fin 6) :
    loadedWord mem aw (ptr + UInt256.ofNat (32 * i.val)) = s.words[i.val] := by
  have hi := i.isLt
  have hb := h.bound
  have hoff : (ptr + UInt256.ofNat (32 * i.val)).toNat = ptr.toNat + 32 * i.val := by
    have hn : (UInt256.ofNat (32 * i.val)).toNat = 32 * i.val :=
      ulit_toNat' _ (by change 32 * i.val < 2 ^ 256; omega)
    change (UInt256.add ptr _).toNat = _
    rw [addWord_toNat ptr _ (by rw [hn]; change _ < 2 ^ 256; omega), hn]
  apply loadedWord_of_read h.active
  · rw [hoff]
    have hs := h.size
    omega
  · rw [hoff]
    have hc := h.cover
    omega
  · rw [hoff]
    exact h.read i

theorem SnapshotMemory.expand_eq {s mem aw ptr} (h : SnapshotMemory s mem aw ptr) (i : Fin 6) :
    expandedWords aw (ptr + UInt256.ofNat (32 * i.val)) ⟨32⟩ = aw := by
  have hi := i.isLt
  have hb := h.bound
  have hoff : (ptr + UInt256.ofNat (32 * i.val)).toNat = ptr.toNat + 32 * i.val := by
    have hn : (UInt256.ofNat (32 * i.val)).toNat = 32 * i.val :=
      ulit_toNat' _ (by change 32 * i.val < 2 ^ 256; omega)
    change (UInt256.add ptr _).toNat = _
    rw [addWord_toNat ptr _ (by rw [hn]; change _ < 2 ^ 256; omega), hn]
  exact expandedWords32_eq_of_cover h.active (by omega) (by have hc := h.cover; omega)

end Auction
