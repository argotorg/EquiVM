import Benchmarks.Auction.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def wordBytes : List UInt256 → ByteArray
  | [] => ByteArray.empty
  | w :: ws => UInt256.toByteArray w ++ wordBytes ws

theorem wordBytes_size (ws : List UInt256) : (wordBytes ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [wordBytes, ByteArray.size_append, toByteArray_size,
      ih, List.length_cons]; omega

theorem wordBytes_append (xs ys : List UInt256) :
    wordBytes (xs ++ ys) = wordBytes xs ++ wordBytes ys := by
  induction xs with
  | nil => simp [wordBytes]
  | cons w ws ih => simp only [List.cons_append, wordBytes, ih, ByteArray.append_assoc]

theorem wordBytes_eq_list (ws : List UInt256) :
    wordBytes ws = (ws.flatMap EVM.Word.toBytesBE).toByteArray := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordBytes, List.flatMap_cons, list_toByteArray_append,
      word_toBytesBE_toByteArray_eq_toByteArray, ih]

def returnMem (ws : List UInt256) : ByteArray :=
  (solcFreePtrMem ++ ffi.ByteArray.zeroes 32) ++ wordBytes ws

theorem returnMem_size (ws : List UInt256) : (returnMem ws).size = 128 + 32 * ws.length := by
  rw [returnMem, ByteArray.size_append, solcFreePtrMem_pad_size, wordBytes_size]

theorem returnMem_single (w : UInt256) : solcReturnMem w = returnMem [w] := by
  simpa only [returnMem, wordBytes, ByteArray.append_empty] using solcReturnMem_eq w

theorem returnMem_write (ws : List UInt256) (w : UInt256) :
    (UInt256.toByteArray w).write 0 (returnMem ws) (128 + 32 * ws.length) 32 =
      returnMem (ws ++ [w]) := by
  rw [← returnMem_size ws, write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]),
    toByteArray_extract_all]
  simp only [returnMem, wordBytes_append, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

theorem returnMem_read64 (ws : List UInt256) :
    (returnMem ws).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by rw [returnMem_size]; omega), returnMem,
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_pad_size]; omega),
    extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ _ (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem returnMem_read128 (ws : List UInt256) (hpos : 0 < ws.length)
    (hsize : 32 * ws.length < 2 ^ 64) :
    (returnMem ws).readWithPadding 128 (32 * ws.length) = wordBytes ws := by
  rw [readWithPadding_eq_extract' _ _ _ (by omega) hsize (by rw [returnMem_size])]
  exact extract_append_right' _ _ _ _ (by rw [solcFreePtrMem_pad_size])
    (by rw [solcFreePtrMem_pad_size, wordBytes_size])

end Auction
