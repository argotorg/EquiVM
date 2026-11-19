import Benchmarks.Midnight.ByteCopyMemory
import Benchmarks.Midnight.SafeTransferOutputBudget

/-! Memory windows used by the multicall input and return-data copies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a calldata copy followed by a zero word, including empty input.
theorem copyZeroMemory_size_or_empty (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : len = 0 ∨ srcOff + len ≤ src.size) :
    (copyZeroMemory src mem srcOff dest len).size = max mem.size (dest + len + 32) := by
  by_cases hz : len = 0
  · simp only [hz, copyZeroMemory, byteArray_write_len_zero, Nat.add_zero,
      writeWord_sparse_size]
  · exact copyZeroMemory_size src mem srcOff dest len hz (hsrc.resolve_left hz)

theorem copyZeroMemory_read_or_empty (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : len = 0 ∨ srcOff + len ≤ src.size) (hsmall : len < 2^64) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding dest len =
      src.readWithPadding srcOff len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  · exact copyZeroMemory_read src mem srcOff dest len (by omega) (hsrc.resolve_left hz) hsmall

theorem copyZeroMemory_prefix_or_empty (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hsrc : len = 0 ∨ srcOff + len ≤ src.size) (hb : limit ≤ dest) :
    MemoryPrefix mem (copyZeroMemory src mem srcOff dest len) limit := by
  by_cases hz : len = 0
  · simp only [hz, copyZeroMemory, byteArray_write_len_zero, Nat.add_zero]
    exact memoryPrefix_writeWord _ _ _ _ (Or.inl hb)
  · exact copyZeroMemory_prefix src mem srcOff dest len limit hz (hsrc.resolve_left hz) hb

theorem copyZeroMemory_load_before_or_empty (src mem : ByteArray) (srcOff dest len : Nat)
    (read : UInt256) (hsrc : len = 0 ∨ srcOff + len ≤ src.size)
    (hin : read.toNat + 32 ≤ mem.size) (hb : read.toNat + 32 ≤ dest) :
    memLoad read (copyZeroMemory src mem srcOff dest len) = memLoad read mem := by
  by_cases hz : len = 0
  · simp only [hz, copyZeroMemory, byteArray_write_len_zero, Nat.add_zero]
    exact memLoad_writeWord_preserved _ _ _ _ hin (Or.inl hb)
  · exact copyZeroMemory_load_before src mem srcOff dest len read hz
      (hsrc.resolve_left hz) hin hb

theorem copySparse_load_before_or_empty (src mem : ByteArray) (srcOff dest len : Nat)
    (read : UInt256) (hsrc : len = 0 ∨ srcOff + len ≤ src.size)
    (hin : read.toNat + 32 ≤ mem.size) (hb : read.toNat + 32 ≤ dest) :
    memLoad read (src.write srcOff mem dest len) = memLoad read mem := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  · unfold memLoad
    rw [if_neg (by rw [copySparse_size _ _ _ _ _ hz (hsrc.resolve_left hz)]; omega),
      if_neg (by omega)]
    rw [copySparse_read_before _ _ _ _ _ _ _ hz (hsrc.resolve_left hz) (by decide) hin hb]

def multicallOutputWork (input : Nat) (out : ByteArray) : Nat :=
  167 + 3 * ((input + 31) / 32) + 3 * ((out.size + 31) / 32) +
    if out.size ≤ max 1024 input then 0 else memoryCost ((out.size + 31) / 32)

theorem multicallOutputWork_growth (input : Nat) (out : ByteArray) :
    4 * ((if out.size = 0 then 0 else returnDataAllocation out.size) / 32) ≤
      multicallOutputWork input out := by
  unfold multicallOutputWork returnDataAllocation memoryCost
  split <;> split <;> omega

end Benchmarks.Midnight
