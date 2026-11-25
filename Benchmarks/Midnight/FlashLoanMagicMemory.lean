import Benchmarks.Midnight.CalldataArrayWords
import Benchmarks.Midnight.MemoryWords
import Benchmarks.Midnight.RuntimeBlocks_062

/-! The callback magic constant and the temporary scratch word used to compare it. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def flashLoanMagic : UInt256 :=
  UInt256.ofNat 0x7f87788ea698181ea4d28d1576d0ba4fc92c0dbe5bf75b43692af2ce91dbaea2

theorem flashLoanMagic_copy (mem : ByteArray) :
    midnightBytecode.write 24513 mem 0 32 = writeWord mem 0 flashLoanMagic := by
  have hb : 24513 + 32 ≤ midnightBytecode.size := by native_decide
  have he : midnightBytecode.extract 24513 (24513 + 32) = flashLoanMagic.toByteArray :=
    by native_decide
  unfold Reasoning.Theory.writeWord
  rw [copyWindow_eq _ _ _ _ _ (by decide) hb (Nat.zero_le _),
    copyWindow_eq _ _ _ _ _ (by decide) (by rw [toByteArray_size]) (Nat.zero_le _), he]
  simp only [Nat.zero_add, toByteArray_extract_all]

def flashLoanMagicMemory (mem : ByteArray) : ByteArray :=
  writeWord (writeWord mem 0 flashLoanMagic) 0 (memLoad ⟨0⟩ mem)

theorem flashLoanMagic_load (mem : ByteArray) :
    memLoad ⟨0⟩ (writeWord mem 0 flashLoanMagic) = flashLoanMagic :=
  memLoad_writeWord mem ⟨0⟩ flashLoanMagic

theorem flashLoanMagicMemory_size (mem : ByteArray) (hm : 32 ≤ mem.size) :
    (flashLoanMagicMemory mem).size = mem.size := by
  rw [flashLoanMagicMemory, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem flashLoanMagicMemory_load (mem : ByteArray) (read : UInt256)
    (hl : 32 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (flashLoanMagicMemory mem) = memLoad read mem := by
  rw [flashLoanMagicMemory,
    memLoad_writeWord_preserved _ _ _ _ (by rw [writeWord_sparse_size]; omega) (Or.inr hl),
    memLoad_writeWord_preserved _ _ _ _ hin (Or.inr hl)]

end Benchmarks.Midnight
