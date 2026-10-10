import Benchmarks.UniswapV3.Pool.TupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

-- GENERALIZES Reasoning.HeapMemory.returnMem to a preserved 96-byte scratch prefix.
def scratchReturnMem (scratch : ByteArray) (ws : List UInt256) : ByteArray :=
  scratch ++ ByteArray.zeroes 32 ++ wordBytes ws

theorem scratchReturnMem_size (scratch : ByteArray) (ws : List UInt256)
    (hs : scratch.size = 96) : (scratchReturnMem scratch ws).size = 128 + 32 * ws.length := by
  simp only [scratchReturnMem, ByteArray.size_append, ByteArray_zeroes_size, wordBytes_size, hs]

theorem scratchReturnMem_single (scratch : ByteArray) (w : UInt256)
    (hs : scratch.size = 96) :
    w.toByteArray.write 0 scratch 128 32 = scratchReturnMem scratch [w] := by
  rw [toByteArray_write_eq _ _ 128 (by omega) (by rw [hs]; exact lt_usize _ (by norm_num))]
  simp only [hs, scratchReturnMem, wordBytes, ByteArray.append_empty, Nat.reduceSub]

theorem scratchReturnMem_write (scratch : ByteArray) (ws : List UInt256) (w : UInt256)
    (hs : scratch.size = 96) (off : Nat) (hoff : off = 128 + 32 * ws.length) :
    w.toByteArray.write 0 (scratchReturnMem scratch ws) off 32 =
      scratchReturnMem scratch (ws ++ [w]) := by
  rw [hoff, ← scratchReturnMem_size scratch ws hs,
    write_at_end_eq _ _ 32 (by decide) (by rw [toByteArray_size]), toByteArray_extract_all]
  simp only [scratchReturnMem, wordBytes_append, wordBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

theorem scratchReturnMem_mload64 (scratch : ByteArray) (ws : List UInt256)
    (hs : scratch.size = 96)
    (hr : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    memLoad (UInt256.ofNat 64) (scratchReturnMem scratch ws) = ⟨128⟩ := by
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [scratchReturnMem_size scratch ws hs]
    omega
  · change (scratchReturnMem scratch ws).readWithPadding 64 32 = _
    rw [readWithPadding_eq_extract _ _ (by rw [scratchReturnMem_size scratch ws hs]; omega),
      scratchReturnMem,
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hs, ByteArray_zeroes_size]; decide),
      extract_append_left _ _ _ _ (by rw [hs]),
      ← readWithPadding_eq_extract _ _ (by rw [hs]), hr]

theorem scratchReturnMem_read128 (scratch : ByteArray) (ws : List UInt256)
    (hs : scratch.size = 96) (hpos : 0 < ws.length) (hsize : 32 * ws.length < 2 ^ 64) :
    (scratchReturnMem scratch ws).readWithPadding 128 (32 * ws.length) = wordBytes ws := by
  rw [readWithPadding_eq_extract' _ _ _ (by omega) hsize
    (by rw [scratchReturnMem_size scratch ws hs])]
  exact extract_append_right' _ _ _ _
    (by rw [ByteArray.size_append, hs, ByteArray_zeroes_size])
    (by rw [ByteArray.size_append, hs, ByteArray_zeroes_size, wordBytes_size])

end Benchmarks.UniswapV3.Pool
