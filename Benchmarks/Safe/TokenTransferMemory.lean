import Benchmarks.Safe.TokenTransferSource
import Benchmarks.Safe.SelectorPatchMemory
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def transferSelectorWord : UInt256 := UInt256.shiftLeft ⟨2835717307⟩ ⟨224⟩

def tokenTransferArgsMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  writeWord (writeWord mem (ptr + 36) receiver) (ptr + 68) amount

def tokenTransferHeaderMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  writeWord (writeWord (tokenTransferArgsMemory mem ptr receiver amount) ptr ⟨68⟩) 64
    (UInt256.ofNat (ptr + 100))

def tokenTransferMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  transferSelectorWord.toByteArray.write 0 (tokenTransferHeaderMemory mem ptr receiver amount)
    (ptr + 32) 4

theorem tokenTransferArgsMemory_size (mem : ByteArray) (ptr : Nat)
    (receiver amount : UInt256) :
    (tokenTransferArgsMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  simp only [tokenTransferArgsMemory, writeWord_sparse_size]
  omega

theorem tokenTransferHeaderMemory_size (mem : ByteArray) (ptr : Nat)
    (receiver amount : UInt256) :
    (tokenTransferHeaderMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  simp only [tokenTransferHeaderMemory, writeWord_sparse_size, tokenTransferArgsMemory_size]
  omega

theorem tokenTransferMemory_size (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    (tokenTransferMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  rw [tokenTransferMemory, copyWindow_size _ _ _ _ _ (by decide) (by simp)
      (by rw [tokenTransferHeaderMemory_size]; omega), tokenTransferHeaderMemory_size]
  omega

theorem tokenTransferArgsMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (receiver amount : UInt256) (hin : off + count ≤ mem.size) (hh : off + count ≤ ptr) :
    (tokenTransferArgsMemory mem ptr receiver amount).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [tokenTransferArgsMemory, writeWordReadBelow _ _ _ _ _ (by
    rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin (by omega)]

theorem tokenTransferArgsMemory_free {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (tokenTransferArgsMemory mem ptr receiver amount) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    tokenTransferArgsMemory_preserved _ _ _ _ _ _ hm hp,
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

theorem tokenTransferMemory_free (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (tokenTransferMemory mem ptr receiver amount) = UInt256.ofNat (ptr + 100) := by
  apply memLoad_of_wordRead
  change (tokenTransferMemory mem ptr receiver amount).readWithPadding 64 32 = _
  rw [tokenTransferMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
    (by rw [tokenTransferHeaderMemory_size]; omega) (by omega)]
  exact writeWord_sparse_read_back _ _ _

theorem tokenTransferMemory_length (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (hp : 96 ≤ ptr) :
    (tokenTransferMemory mem ptr receiver amount).readWithPadding ptr 32 =
      (⟨68⟩ : UInt256).toByteArray := by
  rw [tokenTransferMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
      (by rw [tokenTransferHeaderMemory_size]; omega) (by omega),
    tokenTransferHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size]; omega) hp, writeWord_sparse_read_back]

theorem tokenTransferMemory_preserved (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    MemoryPreserves mem (tokenTransferMemory mem ptr receiver amount) 96 ptr := by
  refine ⟨by rw [tokenTransferMemory_size]; omega, ?_⟩
  intro off count hl hh hin
  rw [tokenTransferMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
      (by rw [tokenTransferHeaderMemory_size]; omega) (by omega),
    tokenTransferHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size, tokenTransferArgsMemory_size]; omega) hl,
    writeWordReadBelow _ _ _ _ _ (by rw [tokenTransferArgsMemory_size]; omega) hh,
    tokenTransferArgsMemory_preserved _ _ _ _ _ _ hin hh]

theorem tokenTransferMemory_read (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (hp : 96 ≤ ptr) :
    (tokenTransferMemory mem ptr receiver amount).readWithPadding (ptr + 32) 68 =
      transferSelector ++ receiver.toByteArray ++ amount.toByteArray := by
  have hs := tokenTransferMemory_size mem ptr receiver amount
  have hsel : (tokenTransferMemory mem ptr receiver amount).readWithPadding (ptr + 32) 4 =
      transferSelector := by
    rw [tokenTransferMemory, copySlice_read _ _ _ _ _ (by simp)
      (by rw [tokenTransferHeaderMemory_size]; omega)]
    decide +kernel
  have hword (off : Nat) (hh : ptr + 36 ≤ off) (hi : off + 32 ≤ ptr + 100) :
      (tokenTransferMemory mem ptr receiver amount).readWithPadding off 32 =
        (tokenTransferArgsMemory mem ptr receiver amount).readWithPadding off 32 := by
    rw [tokenTransferMemory, copyWindowReadAbove _ _ _ _ _ _ _ (by simp)
        (by rw [tokenTransferHeaderMemory_size]; omega)
        (by rw [tokenTransferHeaderMemory_size]; omega) (by omega),
      tokenTransferHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
        rw [writeWord_sparse_size, tokenTransferArgsMemory_size]; omega) (by omega),
      writeWordReadAbove _ _ _ _ _ (by rw [tokenTransferArgsMemory_size]; omega) (by omega)]
  have hr : (tokenTransferMemory mem ptr receiver amount).readWithPadding (ptr + 36) 32 =
      receiver.toByteArray := by
    rw [hword _ (by omega) (by omega), tokenTransferArgsMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
  have ha : (tokenTransferMemory mem ptr receiver amount).readWithPadding (ptr + 68) 32 =
      amount.toByteArray := by
    rw [hword _ (by omega) (by omega), tokenTransferArgsMemory, writeWord_sparse_read_back]
  rw [show 68 = 4 + (32 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 4 64 (by decide) (by decide) (by omega),
    show ptr + 32 + 4 = ptr + 36 by omega,
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide) (by omega),
    show ptr + 36 + 32 = ptr + 68 by omega, hsel, hr, ha, ByteArray.append_assoc]

end Benchmarks.Safe
