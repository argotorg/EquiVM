import Benchmarks.UniswapV3.Pool.WordArrayPrefix
import Benchmarks.UniswapV3.Pool.MemoryGasBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: copying past the source end preserves existing lower reads.
theorem zeroCopy_read_below (src mem : ByteArray) (srcOff dest len read : Nat)
    (hs : src.size ≤ srcOff) (hd : read + 32 ≤ dest) (hin : read + 32 ≤ mem.size) :
    (src.write srcOff mem dest len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hm := byteArray_write_size_ge_base src mem srcOff dest len
  rw [readWithPadding_eq_extract _ read (by omega), readWithPadding_eq_extract _ read hin]
  by_cases hz : len = 0
  · subst len; rw [byteArray_write_len_zero]
  · apply ByteArray.ext
    have hdata : mem.data.size = mem.size := rfl
    simp only [ByteArray.write, if_neg hz, if_pos hs, ByteArray.data_extract, ByteArray.data_copySlice]
    rw [Array.extract_append_of_stop_le_size_left
        (by simp only [Array.size_append, Array.size_extract]; change _ ≤ _; omega),
      Array.extract_append_of_stop_le_size_left
        (by simp only [Array.size_extract]; change _ ≤ _; omega),
      Array.extract_extract]
    congr 1 <;> omega

theorem zeroCopy_prefix (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hs : src.size ≤ srcOff) (hd : limit ≤ dest) :
    MemoryPrefix mem (src.write srcOff mem dest len) limit :=
  ⟨byteArray_write_size_ge_base src mem srcOff dest len,
    fun read _ hb hin ↦ zeroCopy_read_below src mem srcOff dest len read hs (by omega) hin⟩

theorem zeroCopy_cursor {mem : ByteArray} {aw free : UInt256} (hm : MemoryCursor mem aw free)
    (src : ByteArray) (srcOff dest len : Nat) (hs : src.size ≤ srcOff) (hd : 96 ≤ dest) :
    MemoryCursor (src.write srcOff mem dest len) aw free := by
  refine ⟨le_trans hm.size (byteArray_write_size_ge_base src mem srcOff dest len), ?_, hm.lower, hm.active⟩
  rw [zeroCopy_read_below src mem srcOff dest len 64 hs hd hm.size, hm.free]

-- LIBRARY CANDIDATE: reserve a variable amount while keeping addresses below the memory bound.
theorem memoryGasReserveOrOOG {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc aw p : UInt256} {stack : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {k C allowance reserve : Nat} (rd : RD code ee g s0 pc stack mem aw rdata σ k C)
    (h : MemoryGasBound aw C allowance) (ha : allowance ≤ 2 ^ 200)
    (hp : p.toNat ≤ aw.toNat * 32 + 32) (hr : reserve ≤ 2 ^ 199) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ p.toNat + reserve ≤ 2 ^ 200 := by
  rcases rd with hoog | ⟨s, _, _, _, _, _, _, hc, _⟩
  · exact Or.inl hoog
  · have hwords := h.words_lt hc ha
    exact Or.inr (by omega)

end Benchmarks.UniswapV3.Pool
