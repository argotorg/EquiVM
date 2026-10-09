import Benchmarks.Safe.ExecGuardCallEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def execGuardSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1978710866))
    (UInt256.ofNat 224)

def execGuardCallMemory (cd mem : ByteArray) (ptr src : Nat) (p : ExecTransactionInput)
    (sender : UInt256) (words : List UInt256) : ByteArray :=
  execGuardArgsMemory cd (writeWord mem ptr execGuardSelectorWord) (ptr + 4) src p.tx
    sender p.signatures.size words

theorem execGuardCallMemory_size (cd mem : ByteArray) (ptr src : Nat)
    (p : ExecTransactionInput) (sender : UInt256) (words : List UInt256)
    (hin : src + p.tx.payload.size ≤ cd.size)
    (hn : words.length = (p.signatures.size + 31) / 32) :
    (execGuardCallMemory cd mem ptr src p sender words).size =
      max mem.size (ptr + 452 + ABI.paddedSize p.tx.payload.size + p.signatures.size) := by
  rw [execGuardCallMemory, execGuardArgsMemory_size _ _ _ _ _ _ _ _ hin hn,
    writeWord_sparse_size]
  omega

theorem execGuardCallMemory_preserves (cd mem : ByteArray) (ptr src : Nat)
    (p : ExecTransactionInput) (sender : UInt256) (words : List UInt256)
    (hin : src + p.tx.payload.size ≤ cd.size)
    (hn : words.length = (p.signatures.size + 31) / 32) :
    MemoryPreserves mem (execGuardCallMemory cd mem ptr src p sender words) 0 ptr := by
  refine ⟨by rw [execGuardCallMemory_size _ _ _ _ _ _ _ hin hn]; omega, ?_⟩
  intro off count hl hb hm
  rw [execGuardCallMemory, (execGuardArgsMemory_preserves _ _ _ _ _ _ _ _ hin hn).read
    off count hl (by omega) (by rw [writeWord_sparse_size]; omega),
    writeWordReadBelow _ _ _ _ _ hm hb]

theorem execGuardCallMemory_read (cd mem : ByteArray) (ptr src : Nat)
    (p : ExecTransactionInput) (sender : UInt256) (words : List UInt256)
    (hin : src + p.tx.payload.size ≤ cd.size)
    (hd : cd.extract src (src + p.tx.payload.size) = p.tx.payload)
    (hn : words.length = (p.signatures.size + 31) / 32)
    (hp : (wordBytes words).extract 0 p.signatures.size = p.signatures) :
    (execGuardCallMemory cd mem ptr src p sender words).readWithPadding ptr
      (420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size) =
      checkTransactionSelector ++ execGuardArgsBytes p.tx p.signatures sender := by
  have hs := execGuardCallMemory_size cd mem ptr src p sender words hin hn
  have hsel : (execGuardCallMemory cd mem ptr src p sender words).readWithPadding ptr 4 =
      checkTransactionSelector := by
    rw [execGuardCallMemory, (execGuardArgsMemory_preserves _ _ _ _ _ _ _ _ hin hn).read
      ptr 4 (by omega) (by omega) (by rw [writeWord_sparse_size]; omega)]
    have hr := writeWord_sparse_read_window mem ptr 0 4 execGuardSelectorWord
      (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add,
      show execGuardSelectorWord.toByteArray.extract 0 4 = checkTransactionSelector
        from by decide +kernel] using hr
  rw [show 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size =
      4 + (416 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by unfold ABI.paddedSize at *; omega), hsel, execGuardCallMemory,
    execGuardArgsMemory_read _ _ _ _ _ _ _ _ hin hd hn hp]

end Benchmarks.Safe
