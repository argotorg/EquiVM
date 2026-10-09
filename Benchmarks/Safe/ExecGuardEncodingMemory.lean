import Benchmarks.Safe.CalldataBytesEncodingInto
import Benchmarks.Safe.MemoryBytesEncodingInto
import Benchmarks.Safe.TransactionHashSource
import Benchmarks.Safe.Decoders

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def execGuardHeadWords (tx : SafeTransaction) : List UInt256 :=
  [UInt256.land (UInt256.ofNat tx.target.val) solcAddrMask, tx.value, ⟨352⟩]

def execGuardMiddleWords (tx : SafeTransaction) : List UInt256 :=
  [tx.operation, tx.safeTxGas, tx.baseGas, tx.gasPrice,
    UInt256.land solcAddrMask (UInt256.ofNat tx.gasToken.val),
    UInt256.land (UInt256.ofNat tx.refundReceiver.val) solcAddrMask,
    UInt256.ofNat (384 + ABI.paddedSize tx.payload.size)]

def execGuardHeadMemory (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction) :
    ByteArray :=
  calldataBytesEncodedInto cd (writeWords mem base (execGuardHeadWords tx))
    src (base + 352) tx.payload.size

def execGuardPrefixMemory (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction) :
    ByteArray :=
  writeWords (execGuardHeadMemory cd mem base src tx) (base + 96) (execGuardMiddleWords tx)

def execGuardArgsMemory (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction)
    (sender : UInt256) (sigLen : Nat) (words : List UInt256) : ByteArray :=
  writeWord (memoryBytesEncodedInto (execGuardPrefixMemory cd mem base src tx)
    (base + 384 + ABI.paddedSize tx.payload.size) sigLen words)
    (base + 320) (UInt256.land solcAddrMask sender)

theorem execGuardHeadMemory_size (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction)
    (hin : src + tx.payload.size ≤ cd.size) :
    (execGuardHeadMemory cd mem base src tx).size = max mem.size (base + 416 + tx.payload.size) :=
    by
  rw [execGuardHeadMemory, calldataBytesEncodedInto_size _ _ _ _ _ hin,
    writeWords_size_nonempty _ _ _ (by simp [execGuardHeadWords])]
  simp only [execGuardHeadWords, List.length_cons, List.length_nil]
  omega

theorem execGuardPrefixMemory_size (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction)
    (hin : src + tx.payload.size ≤ cd.size) :
    (execGuardPrefixMemory cd mem base src tx).size =
      max mem.size (base + 416 + tx.payload.size) := by
  rw [execGuardPrefixMemory, writeWords_size_nonempty _ _ _
    (by simp [execGuardMiddleWords]), execGuardHeadMemory_size _ _ _ _ _ hin]
  simp only [execGuardMiddleWords, List.length_cons, List.length_nil]
  omega

theorem execGuardHeadMemory_preserves (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (hin : src + tx.payload.size ≤ cd.size) :
    MemoryPreserves mem (execGuardHeadMemory cd mem base src tx) 0 base := by
  refine ⟨by rw [execGuardHeadMemory_size _ _ _ _ _ hin]; omega, ?_⟩
  intro off count _ hb hm
  rw [execGuardHeadMemory, (calldataBytesEncodedInto_preserves _ _ _ _ _ hin).read
    off count (by omega) (by omega) (by
      rw [writeWords_size_nonempty _ _ _ (by simp [execGuardHeadWords])]; omega),
    writeWords_readBelow _ _ _ _ _ hm hb]

theorem execGuardPrefixMemory_preserves (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (hin : src + tx.payload.size ≤ cd.size) :
    MemoryPreserves mem (execGuardPrefixMemory cd mem base src tx) 0 base := by
  have hp := execGuardHeadMemory_preserves cd mem base src tx hin
  refine ⟨by rw [execGuardPrefixMemory_size _ _ _ _ _ hin]; omega, ?_⟩
  intro off count hl hb hm
  rw [execGuardPrefixMemory, writeWords_readBelow _ _ _ _ _ (hm.trans hp.size) (by omega)]
  exact hp.read off count hl hb hm

theorem execGuardArgsMemory_size (cd mem : ByteArray) (base src : Nat) (tx : SafeTransaction)
    (sender : UInt256) (sigLen : Nat) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size) (hn : words.length = (sigLen + 31) / 32) :
    (execGuardArgsMemory cd mem base src tx sender sigLen words).size =
      max mem.size (base + 448 + ABI.paddedSize tx.payload.size + sigLen) := by
  rw [execGuardArgsMemory, writeWord_sparse_size, memoryBytesEncodedInto_size _ _ _ _ hn,
    execGuardPrefixMemory_size _ _ _ _ _ hin]
  unfold ABI.paddedSize
  omega

theorem execGuardArgsMemory_preserves (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (sender : UInt256) (sigLen : Nat) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size) (hn : words.length = (sigLen + 31) / 32) :
    MemoryPreserves mem (execGuardArgsMemory cd mem base src tx sender sigLen words) 0 base := by
  have hp := execGuardPrefixMemory_preserves cd mem base src tx hin
  refine ⟨by rw [execGuardArgsMemory_size _ _ _ _ _ _ _ _ hin hn]; omega, ?_⟩
  intro off count hl hb hm
  rw [execGuardArgsMemory, writeWordReadBelow _ _ _ _ _ (by
    rw [memoryBytesEncodedInto_size _ _ _ _ hn]; have := hp.size; omega) (by omega),
    memoryBytesEncodedInto_preserved _ _ _ _ _ _ (hm.trans hp.size) (by omega)]
  exact hp.read off count hl hb hm

end Benchmarks.Safe
