import Benchmarks.UniswapV3.Pool.Common
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: consecutive scalar memory writes and struct allocation.
def writeWordArray (mem : ByteArray) (off : Nat) : List UInt256 → ByteArray
  | [] => mem
  | w :: ws => writeWordArray (writeWord mem off w) (off + 32) ws

theorem writeWordArray_size_mono (mem : ByteArray) (off : Nat) (ws : List UInt256) :
    mem.size ≤ (writeWordArray mem off ws).size := by
  induction ws generalizing mem off with
  | nil => exact le_refl _
  | cons w ws ih =>
      exact le_trans (by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _) (ih _ _)

theorem writeWordArray_size (mem : ByteArray) (off : Nat) (ws : List UInt256) (hn : ws ≠ []) :
    (writeWordArray mem off ws).size = max mem.size (off + 32 * ws.length) := by
  induction ws generalizing mem off with
  | nil => exact False.elim (hn rfl)
  | cons w ws ih =>
      cases ws with
      | nil => simp only [writeWordArray, writeWord_sparse_size, List.length_cons, List.length_nil]
      | cons v vs =>
          rw [writeWordArray, ih _ _ (by simp), writeWord_sparse_size]
          simp only [List.length_cons]
          omega

theorem writeWordArray_preserve_below (mem : ByteArray) (off readOff : Nat) (ws : List UInt256)
    (hbelow : readOff + 32 ≤ off) (hin : readOff + 32 ≤ mem.size) :
    (writeWordArray mem off ws).readWithPadding readOff 32 = mem.readWithPadding readOff 32 := by
  induction ws generalizing mem off with
  | nil => rfl
  | cons w ws ih =>
      rw [writeWordArray, ih _ _ (by omega) (by rw [writeWord_sparse_size]; omega),
        writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hbelow, hin⟩)]

theorem writeWordArray_read (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (i : Nat) (hi : i < ws.length) :
    (writeWordArray mem off ws).readWithPadding (off + 32 * i) 32 = ws[i].toByteArray := by
  induction ws generalizing mem off i with
  | nil => simp at hi
  | cons w ws ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, writeWordArray]
          rw [writeWordArray_preserve_below _ _ _ _ (by omega)
            (by rw [writeWord_sparse_size]; omega), writeWord_sparse_read_back]
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          simpa only [writeWordArray, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (writeWord mem off w) (off + 32) i hi'

theorem writeWordArray_prefix (mem : ByteArray) (off limit : Nat) (ws : List UInt256)
    (hbelow : limit ≤ off) : MemoryPrefix mem (writeWordArray mem off ws) limit := by
  induction ws generalizing mem off with
  | nil => exact .refl _ _
  | cons w ws ih =>
      exact (memoryPrefix_sparse_writeWord mem off limit w (Or.inl hbelow)).trans
        (ih _ _ (by omega))

def wordArrayAllocMem (mem : ByteArray) (p : UInt256) (ws : List UInt256) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + UInt256.ofNat (32 * ws.length))) p.toNat ws

theorem wordArrayAllocMem_size (mem : ByteArray) (p : UInt256) (ws : List UInt256)
    (hp : 128 ≤ p.toNat) (hn : ws ≠ []) :
    (wordArrayAllocMem mem p ws).size = max mem.size (p.toNat + 32 * ws.length) := by
  rw [wordArrayAllocMem, writeWordArray_size _ _ _ hn, writeWord_sparse_size]
  omega

theorem wordArrayAllocMem_read (mem : ByteArray) (p : UInt256) (ws : List UInt256)
    (i : Nat) (hi : i < ws.length) :
    (wordArrayAllocMem mem p ws).readWithPadding (p.toNat + 32 * i) 32 = ws[i].toByteArray :=
  writeWordArray_read _ _ ws i hi

theorem wordArrayAllocMem_free (mem : ByteArray) (p : UInt256) (ws : List UInt256)
    (hp : 128 ≤ p.toNat) :
    (wordArrayAllocMem mem p ws).readWithPadding 64 32 =
      (p + UInt256.ofNat (32 * ws.length)).toByteArray := by
  rw [wordArrayAllocMem, writeWordArray_preserve_below _ _ _ _ (by omega)
    (by rw [writeWord_sparse_size]; omega), writeWord_sparse_read_back]

theorem wordArrayAllocMem_prefix (mem : ByteArray) (p : UInt256) (ws : List UInt256) :
    MemoryPrefix mem (wordArrayAllocMem mem p ws) p.toNat :=
  (memoryPrefix_sparse_writeWord mem 64 p.toNat _ (Or.inr (by decide))).trans
    (writeWordArray_prefix _ _ _ ws (le_refl _))

theorem wordArrayAllocMem_heap (mem : ByteArray) (p aw : UInt256) (ws : List UInt256)
    (hp : 128 ≤ p.toNat) (hn : ws ≠ []) (hb : p.toNat + 32 * ws.length ≤ 2 ^ 200)
    (ha : ActiveWords aw) :
    HeapMemory (wordArrayAllocMem mem p ws) aw (p + UInt256.ofNat (32 * ws.length)) := by
  have hnext : (p + UInt256.ofNat (32 * ws.length)).toNat = p.toNat + 32 * ws.length :=
    uadd_word_ofNat_toNat p _ (by change _ < 2 ^ 256; omega)
  refine ⟨?_, wordArrayAllocMem_free mem p ws hp, ?_, ?_, ha⟩
  · rw [wordArrayAllocMem_size mem p ws hp hn]; omega
  · rw [hnext]; omega
  · rw [hnext, wordArrayAllocMem_size mem p ws hp hn]; omega


structure WordArrayMemory (mem : ByteArray) (p : UInt256) (ws : List UInt256) : Prop where
  size : p.toNat + 32 * ws.length ≤ mem.size
  read : ∀ i (hi : i < ws.length),
    mem.readWithPadding (p.toNat + 32 * i) 32 = ws[i].toByteArray

theorem wordArrayAllocMem_region (mem : ByteArray) (p : UInt256) (ws : List UInt256)
    (hp : 128 ≤ p.toNat) (hn : ws ≠ []) :
    WordArrayMemory (wordArrayAllocMem mem p ws) p ws :=
  ⟨by rw [wordArrayAllocMem_size mem p ws hp hn]; omega,
    wordArrayAllocMem_read mem p ws⟩

theorem WordArrayMemory.load {mem : ByteArray} {p : UInt256} {ws : List UInt256}
    (hm : WordArrayMemory mem p ws) (i : Nat) (hi : i < ws.length)
    (hb : p.toNat + 32 * ws.length < UInt256.size) :
    memLoad (p + UInt256.ofNat (32 * i)) mem = ws[i] := by
  have hoff : (p + UInt256.ofNat (32 * i)).toNat = p.toNat + 32 * i :=
    uadd_word_ofNat_toNat p _ (by omega)
  apply mloadWordValue_of_readWithPadding
  · rw [hoff]; have hs := hm.size; omega
  · rw [hoff]; exact hm.read i hi

theorem MemoryPrefix.wordArray {mem mem' : ByteArray} {p : UInt256} {ws : List UInt256}
    {limit : Nat} (h : MemoryPrefix mem mem' limit) (hm : WordArrayMemory mem p ws)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 32 * ws.length ≤ limit) :
    WordArrayMemory mem' p ws := by
  refine ⟨le_trans hm.size h.size, fun i hi => ?_⟩
  rw [h.read _ (by omega) (by omega) (by have hs := hm.size; omega), hm.read i hi]

end Benchmarks.UniswapV3.Pool
