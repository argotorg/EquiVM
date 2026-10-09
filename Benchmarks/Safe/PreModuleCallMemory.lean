import Benchmarks.Safe.PreModuleCallEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def preModuleSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 960894137) (UInt256.ofNat 225)

def preModuleCallMemory (mem : ByteArray) (ptr len : Nat)
    (target value operation sender : UInt256) (words : List UInt256) : ByteArray :=
  preModuleArgsMemory (writeWord mem ptr preModuleSelectorWord) (ptr + 4) len
    target value operation sender words

theorem preModuleCallMemory_size (mem : ByteArray) (ptr len : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : mem.size ≤ ptr + 164) (hn : words.length = (len + 31) / 32) :
    (preModuleCallMemory mem ptr len target value operation sender words).size =
      ptr + 228 + len := by
  rw [preModuleCallMemory,
    preModuleArgsMemory_size _ _ _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hn]

theorem preModuleCallMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ ptr) :
    (preModuleCallMemory mem ptr len target value operation sender words).readWithPadding
      off count = mem.readWithPadding off count := by
  rw [preModuleCallMemory, preModuleArgsMemory_preserved _ _ _ _ _ _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin ha]

theorem preModuleCallMemory_free (mem : ByteArray) (ptr len : Nat)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (preModuleCallMemory mem ptr len target value operation sender words) =
      memLoad ⟨64⟩ mem := by
  have hr := preModuleCallMemory_preserved mem ptr len 64 32 target value operation sender
    words hm hp
  have hs : 96 ≤ (preModuleCallMemory mem ptr len target value operation sender words).size := by
    simp only [preModuleCallMemory, preModuleArgsMemory, preModuleHeadMemory,
      memoryBytesEncodedMemory, writeWord_sparse_size, ByteArray.size_append]
    omega
  simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    if_neg (show ¬ 64 ≥ mem.size by omega),
    if_neg (show ¬ 64 ≥ (preModuleCallMemory mem ptr len target value operation sender
      words).size by omega), hr]

theorem preModuleCallMemory_read (mem : ByteArray) (ptr : Nat) (payload : ByteArray)
    (target value operation sender : UInt256) (words : List UInt256)
    (hm : mem.size ≤ ptr + 164) (hn : words.length = (payload.size + 31) / 32)
    (hp : (wordBytes words).extract 0 payload.size = payload) :
    (preModuleCallMemory mem ptr payload.size target value operation sender words).readWithPadding
      ptr (196 + 32 * words.length) = preModuleCallBytes target value payload operation sender := by
  have hs := preModuleCallMemory_size mem ptr payload.size target value operation sender words hm hn
  have hsel :
      (preModuleCallMemory mem ptr payload.size target value operation sender words).readWithPadding
        ptr 4 = checkModuleTransactionSelector := by
    rw [preModuleCallMemory, preModuleArgsMemory_preserved _ _ _ _ _ _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by omega)]
    have hr := writeWord_sparse_read_window mem ptr 0 4 preModuleSelectorWord
      (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add,
      show preModuleSelectorWord.toByteArray.extract 0 4 = checkModuleTransactionSelector
        from by decide +kernel] using hr
  have hargs := preModuleArgsMemory_read (writeWord mem ptr preModuleSelectorWord)
    (ptr + 4) payload.size target value operation sender words
    (by rw [writeWord_sparse_size]; omega) hn
  rw [show 196 + 32 * words.length = 4 + (192 + 32 * words.length) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [hn]; omega), hsel]
  change checkModuleTransactionSelector ++
    (preModuleArgsMemory _ _ _ _ _ _ _ _).readWithPadding _ _ = _
  rw [hargs, hp]
  simp only [preModuleCallBytes, ABI.paddedSize, hn, ByteArray.append_assoc]

end Benchmarks.Safe
