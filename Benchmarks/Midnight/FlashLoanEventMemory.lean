import Benchmarks.Midnight.CalldataArrayCopyMemory

/-! The two dynamic arrays in the flash-loan event buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def flashLoanEventMemory (mem bytes : ByteArray) (root tp tn ap an : Nat) : ByteArray :=
  let m0 := writeWord mem root (UInt256.ofNat 64)
  let m1 := calldataArrayEncodeMemory m0 (root + 64) bytes tp tn
  let m2 := writeWord m1 (root + 32) (UInt256.ofNat (96 + 32 * tn))
  calldataArrayCopyMemory m2 (root + 96 + 32 * tn) bytes ap an

theorem flashLoanEventMemory_size (mem bytes : ByteArray) (root tp tn ap an : Nat)
    (hs : ap + 32 * an ≤ bytes.size) :
    (flashLoanEventMemory mem bytes root tp tn ap an).size =
      max mem.size (root + 128 + 32 * tn + 32 * an) := by
  rw [flashLoanEventMemory, calldataArrayCopyMemory_size _ _ _ _ _ hs,
    writeWord_sparse_size, calldataArrayEncodeMemory,
    writeWordArray_size_nonempty _ _ _ (by simp), writeWord_sparse_size]
  simp only [List.length_cons, calldataArrayWords_length]
  omega

theorem flashLoanEventMemory_load_below (mem bytes : ByteArray) (root tp tn ap an : Nat)
    (read : UInt256) (hs : ap + 32 * an ≤ bytes.size)
    (hin : read.toNat + 32 ≤ mem.size) (hbelow : read.toNat + 32 ≤ root) :
    memLoad read (flashLoanEventMemory mem bytes root tp tn ap an) = memLoad read mem := by
  have h0 : mem.size ≤ (writeWord mem root (UInt256.ofNat 64)).size := by
    rw [writeWord_sparse_size]; omega
  have h1 := writeWordArray_size_ge (writeWord mem root (UInt256.ofNat 64)) (root + 64)
    (UInt256.ofNat tn :: calldataArrayWords bytes tn tp)
  have h2 : mem.size ≤
      (writeWord (calldataArrayEncodeMemory (writeWord mem root (UInt256.ofNat 64))
        (root + 64) bytes tp tn) (root + 32) (UInt256.ofNat (96 + 32 * tn))).size := by
    rw [writeWord_sparse_size]
    exact (h0.trans h1).trans (Nat.le_max_left _ _)
  rw [flashLoanEventMemory, calldataArrayCopyMemory_load_preserved _ _ _ _ _ _ hs
      (hin.trans h2) (Or.inl (by omega)), calldataArrayEncodeMemory,
    memLoad_writeWord_preserved _ _ _ _ (hin.trans (h0.trans h1)) (Or.inl (by omega)),
    memLoad_writeWordArray_below _ _ _ _ (hin.trans h0)
      (by omega),
    memLoad_writeWord_preserved _ _ _ _ hin (Or.inl hbelow)]

end Benchmarks.Midnight
