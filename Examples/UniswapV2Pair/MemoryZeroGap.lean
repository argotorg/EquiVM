import Reasoning.Memory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: writing one word after a 32-byte gap fills that gap with zeroes.
theorem writeWord_read_gap32 (base : ByteArray) (word : UInt256) :
    (word.toByteArray.write 0 base (base.size + 32) 32).readWithPadding base.size 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  have hgap : base.size + 32 - base.size < USize.size := by
    have hu := lt_usize 32 (by omega)
    simpa using hu
  rw [toByteArray_write_eq word base (base.size + 32) (by omega) hgap]
  rw [show base.size + 32 - base.size = 32 by omega]
  rw [readWithPadding_eq_extract _ _ (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, ByteArray_zeroes_size]),
    extract_append_right' _ _ _ _ (by omega) (by rw [ByteArray_zeroes_size])]
  exact zero_toByteArray_eq_zeroes32.symm

end UniswapV2Pair
