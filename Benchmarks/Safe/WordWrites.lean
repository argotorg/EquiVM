import Benchmarks.Safe.ByteBufferMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: consecutive word stores in memory, including an existing suffix.
def writeWords (mem : ByteArray) (dst : Nat) : List UInt256 → ByteArray
  | [] => mem
  | w :: ws => writeWords (writeWord mem dst w) (dst + 32) ws

theorem writeWords_size (mem : ByteArray) (dst : Nat) (words : List UInt256)
    (hd : dst ≤ mem.size) :
    (writeWords mem dst words).size = max mem.size (dst + 32 * words.length) := by
  induction words generalizing mem dst with
  | nil => simp only [writeWords, List.length_nil, Nat.mul_zero, Nat.add_zero, max_eq_left hd]
  | cons w ws ih =>
      rw [writeWords, ih _ _ (by rw [writeWord_sparse_size]; omega), writeWord_sparse_size]
      simp only [List.length_cons]
      omega

theorem writeWords_readBelow (mem : ByteArray) (dst off count : Nat) (words : List UInt256)
    (hin : off + count ≤ mem.size) (hb : off + count ≤ dst) :
    (writeWords mem dst words).readWithPadding off count = mem.readWithPadding off count := by
  induction words generalizing mem dst with
  | nil => rfl
  | cons w ws ih =>
      rw [writeWords, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
        writeWordReadBelow _ _ _ _ _ hin hb]

theorem writeWords_readAbove (mem : ByteArray) (dst off count : Nat) (words : List UInt256)
    (hin : off + count ≤ mem.size) (hb : dst + 32 * words.length ≤ off) :
    (writeWords mem dst words).readWithPadding off count = mem.readWithPadding off count := by
  induction words generalizing mem dst with
  | nil => rfl
  | cons w ws ih =>
      have hb' : dst + 32 * (ws.length + 1) ≤ off := hb
      rw [writeWords, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
        writeWordReadAbove _ _ _ _ _ hin (by omega)]

theorem writeWords_view (mem : ByteArray) (dst : Nat) (words : List UInt256) :
    WordArrayMemory (writeWords mem dst words) dst words := by
  induction words generalizing mem dst with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [writeWords, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
          rw [writeWords_readBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
            (by omega), writeWord_sparse_read_back]
      | succ i =>
          have ht := ih (writeWord mem dst w) (dst + 32) i (by simpa using hi)
          simpa only [writeWords, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem writeWords_size_nonempty (mem : ByteArray) (dst : Nat) (words : List UInt256)
    (hn : words ≠ []) :
    (writeWords mem dst words).size = max mem.size (dst + 32 * words.length) := by
  cases words with
  | nil => exact (hn rfl).elim
  | cons w ws =>
      rw [writeWords, writeWords_size _ _ _ (by rw [writeWord_sparse_size]; omega),
        writeWord_sparse_size]
      simp only [List.length_cons]
      omega

theorem writeWords_read (mem : ByteArray) (dst : Nat) (words : List UInt256) :
    (writeWords mem dst words).readWithPadding dst (32 * words.length) = wordBytes words := by
  by_cases hn : words = []
  · subst words
    exact byteArray_readWithPadding_zero mem dst
  · exact WordArrayMemory.read _ _ _ (writeWords_view _ _ _)
      (by rw [writeWords_size_nonempty _ _ _ hn]; omega)

theorem writeWords_atEnd (mem : ByteArray) (dst : Nat) (words : List UInt256)
    (hm : mem.size = dst) : writeWords mem dst words = mem ++ wordBytes words := by
  induction words generalizing mem dst with
  | nil => simp only [writeWords, wordBytes, ByteArray.append_empty]
  | cons w ws ih =>
      rw [writeWords, ih _ _ (by rw [writeWord_sparse_size, hm]; omega),
        show writeWord mem dst w = mem ++ w.toByteArray from writeWordAtEnd mem w hm,
        ByteArray.append_assoc]
      rfl

end Benchmarks.Safe
