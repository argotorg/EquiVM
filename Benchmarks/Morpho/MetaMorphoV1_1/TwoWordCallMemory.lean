import Benchmarks.Morpho.MetaMorphoV1_1.SingleWordCallMemory

/-! Sparse memory encoding for a selector followed by two static ABI words. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: two-word call data without a bound on the old memory extent.
def twoWordCallMem (mem : ByteArray) (ptr : Nat) (selector first second : UInt256) : ByteArray :=
  writeCascade mem [(ptr, selector), (ptr + 4, first), (ptr + 36, second)]

theorem twoWordCallMem_size (mem : ByteArray) (ptr : Nat) (selector first second : UInt256) :
    (twoWordCallMem mem ptr selector first second).size = max mem.size (ptr + 68) := by
  simp only [twoWordCallMem, writeCascade_cons, writeCascade_nil, writeWord_sparse_size]
  omega

theorem twoWordCallMem_read (mem : ByteArray) (ptr : Nat) (selector first second : UInt256) :
    (twoWordCallMem mem ptr selector first second).readWithPadding ptr 68 =
      selector.toByteArray.extract 0 4 ++ (first.toByteArray ++ second.toByteArray) := by
  have hu := lt_usize 4 (by decide)
  have hs : (twoWordCallMem mem ptr selector first second).readWithPadding ptr 4 =
      selector.toByteArray.extract 0 4 := by
    have h := sparseCascade_read_window mem ptr 0 4 selector
      [(ptr + 4, first), (ptr + 36, second)]
      (by
        simp only [WindowDisjointFromWrites]
        exact ⟨by omega, .inl ⟨by omega, by omega⟩,
          by omega, .inl ⟨by omega, by omega⟩, trivial⟩)
      (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add] using h
  have hf : (twoWordCallMem mem ptr selector first second).readWithPadding (ptr + 4) 32 =
      first.toByteArray := by
    apply sparseCascade_read_word _ _ _ [(ptr + 36, second)]
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl
    omega
  have hlast : (twoWordCallMem mem ptr selector first second).readWithPadding (ptr + 36) 32 =
      second.toByteArray := writeWord_sparse_read_back _ _ _
  have hsize := twoWordCallMem_size mem ptr selector first second
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 4 64 (by decide) (by decide) (by omega), hs,
    show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide) (by omega), hf,
    show ptr + 4 + 32 = ptr + 36 from by omega, hlast]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
