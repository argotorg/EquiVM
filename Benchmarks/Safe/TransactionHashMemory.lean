import Benchmarks.Safe.TransactionHashSource
import Benchmarks.Safe.WordWrites
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def domainMemoryAt (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv) : ByteArray :=
  writeWords mem ptr [domainTypehashWord, UInt256.ofNat Ethereum.chainId,
    UInt256.ofNat I.codeOwner.val]

theorem domainMemoryAt_size (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv) :
    (domainMemoryAt mem ptr I).size = max mem.size (ptr + 96) :=
  writeWords_size_nonempty _ _ _ (by simp)

theorem domainMemoryAt_read (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv) :
    (domainMemoryAt mem ptr I).readWithPadding ptr 96 = domainPreimage I := by
  have hr := writeWords_read mem ptr
    [domainTypehashWord, UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val]
  simpa only [List.length_cons, List.length_nil, wordBytes, ByteArray.append_empty,
    domainMemoryAt, domainPreimage, ByteArray.append_assoc] using hr

def transactionStructMemory (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) : ByteArray :=
  writeWords mem ptr (transactionWords tx)

theorem transactionStructMemory_size (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) :
    (transactionStructMemory mem ptr tx).size = max mem.size (ptr + 352) := by
  exact writeWords_size_nonempty _ _ _ (by simp [transactionWords])

theorem transactionStructMemory_read (mem : ByteArray) (ptr : Nat) (tx : SafeTransaction) :
    (transactionStructMemory mem ptr tx).readWithPadding ptr 352 =
      wordBytes (transactionWords tx) := writeWords_read _ _ _

def transactionFinalMemory (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv)
    (tx : SafeTransaction) : ByteArray :=
  writeWord (writeWord (writeWord (transactionStructMemory mem ptr tx) (ptr + 64)
    (transactionStructWord tx)) ptr ⟨6401⟩) (ptr + 32) (domainWord I)

theorem transactionFinalMemory_size (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv)
    (tx : SafeTransaction) :
    (transactionFinalMemory mem ptr I tx).size = max mem.size (ptr + 352) := by
  simp only [transactionFinalMemory, writeWord_sparse_size, transactionStructMemory_size]
  omega

theorem transactionFinalMemory_read (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv)
    (tx : SafeTransaction) :
    (transactionFinalMemory mem ptr I tx).readWithPadding (ptr + 30) 66 =
      transactionPreimage I tx := by
  have hp : (transactionFinalMemory mem ptr I tx).readWithPadding (ptr + 30) 2 =
      ⟨#[0x19, 0x01]⟩ := by
    rw [transactionFinalMemory, writeWordReadBelow _ _ _ _ _ (by
      simp only [writeWord_sparse_size, transactionStructMemory_size]; omega) (by omega)]
    rw [writeWord_sparse_read_window _ ptr 30 2 ⟨6401⟩ (by decide) (by decide) (by decide)]
    decide +kernel
  have hd : (transactionFinalMemory mem ptr I tx).readWithPadding (ptr + 32) 32 =
      (domainWord I).toByteArray := writeWord_sparse_read_back _ _ _
  have ht : (transactionFinalMemory mem ptr I tx).readWithPadding (ptr + 64) 32 =
      (transactionStructWord tx).toByteArray := by
    rw [transactionFinalMemory,
      writeWordReadAbove _ _ _ _ _ (by
        simp only [writeWord_sparse_size, transactionStructMemory_size]; omega) (by omega),
      writeWordReadAbove _ _ _ _ _ (by
        simp only [writeWord_sparse_size, transactionStructMemory_size]; omega) (by omega),
      writeWord_sparse_read_back]
  have hs : ptr + 96 ≤ (transactionFinalMemory mem ptr I tx).size := by
    rw [transactionFinalMemory_size]; omega
  rw [show 66 = 2 + (32 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 2 64 (by decide) (by decide) (by omega),
    show ptr + 30 + 2 = ptr + 32 by omega,
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide) (by omega),
    show ptr + 32 + 32 = ptr + 64 by omega, hp, hd, ht,
    transactionPreimage, ByteArray.append_assoc]

theorem transactionFinalMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (I : ExecutionEnv) (tx : SafeTransaction)
    (hin : off + count ≤ mem.size) (hb : off + count ≤ ptr) :
    (transactionFinalMemory mem ptr I tx).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [transactionFinalMemory,
    writeWordReadBelow _ _ _ _ _ (by
      simp only [writeWord_sparse_size, transactionStructMemory_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by
      simp only [writeWord_sparse_size, transactionStructMemory_size]; omega) hb,
    writeWordReadBelow _ _ _ _ _ (by rw [transactionStructMemory_size]; omega) (by omega)]
  exact writeWords_readBelow _ _ _ _ _ hin hb

end Benchmarks.Safe
