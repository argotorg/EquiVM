import Benchmarks.Safe.ExecGuardEncodingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def execGuardStaticWords (tx : SafeTransaction) (sender : UInt256) : List UInt256 :=
  execGuardHeadWords tx ++ execGuardMiddleWords tx ++ [UInt256.land solcAddrMask sender]

def execGuardArgsBytes (tx : SafeTransaction) (signatures : ByteArray)
    (sender : UInt256) : ByteArray :=
  wordBytes (execGuardStaticWords tx sender) ++
    (UInt256.ofNat tx.payload.size).toByteArray ++ tx.payload ++
    ByteArray.zeroes (ABI.paddedSize tx.payload.size - tx.payload.size) ++
    (UInt256.ofNat signatures.size).toByteArray ++ signatures ++
    ByteArray.zeroes (ABI.paddedSize signatures.size - signatures.size)

theorem execGuardArgsMemory_static (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (sender : UInt256) (sigLen : Nat) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size) (hn : words.length = (sigLen + 31) / 32) :
    (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding base 352 =
      wordBytes (execGuardStaticWords tx sender) := by
  let m := execGuardPrefixMemory cd mem base src tx
  have hm := execGuardPrefixMemory_size cd mem base src tx hin
  have hs := execGuardArgsMemory_size cd mem base src tx sender sigLen words hin hn
  have hh : (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding
      base 96 = wordBytes (execGuardHeadWords tx) := by
    rw [execGuardArgsMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [memoryBytesEncodedInto_size _ _ _ _ hn]; omega) (by omega),
      memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by omega) (by omega),
      execGuardPrefixMemory, writeWords_readBelow _ _ _ _ _
        (by rw [execGuardHeadMemory_size _ _ _ _ _ hin]; omega) (by omega),
      execGuardHeadMemory, (calldataBytesEncodedInto_preserves _ _ _ _ _ hin).read
        base 96 (by omega) (by omega) (by
          rw [writeWords_size_nonempty _ _ _ (by simp [execGuardHeadWords])]
          simp only [execGuardHeadWords, List.length_cons, List.length_nil]; omega)]
    exact writeWords_read _ _ _
  have hmid : (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding
      (base + 96) 224 = wordBytes (execGuardMiddleWords tx) := by
    rw [execGuardArgsMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [memoryBytesEncodedInto_size _ _ _ _ hn]; omega) (by omega),
      memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by omega) (by omega)]
    exact writeWords_read _ _ _
  have hlast : (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding
      (base + 320) 32 = (UInt256.land solcAddrMask sender).toByteArray :=
    writeWord_sparse_read_back _ _ _
  rw [show 352 = 96 + (224 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by omega),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by omega),
    show base + 96 + 224 = base + 320 by omega, hh, hmid, hlast]
  simp only [execGuardStaticWords, execGuardHeadWords, execGuardMiddleWords, List.cons_append,
    List.nil_append, wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

theorem execGuardArgsMemory_data (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (sender : UInt256) (sigLen : Nat) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size) (hn : words.length = (sigLen + 31) / 32) :
    (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding
      (base + 352) (32 + ABI.paddedSize tx.payload.size) =
      (UInt256.ofNat tx.payload.size).toByteArray ++ cd.extract src (src + tx.payload.size) ++
        ByteArray.zeroes (ABI.paddedSize tx.payload.size - tx.payload.size) := by
  have hm := execGuardPrefixMemory_size cd mem base src tx hin
  have hh := execGuardHeadMemory_size cd mem base src tx hin
  rw [execGuardArgsMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [memoryBytesEncodedInto_size _ _ _ _ hn]; unfold ABI.paddedSize at *; omega) (by omega),
    memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by unfold ABI.paddedSize at *; omega)
      (by omega), execGuardPrefixMemory,
    writeWords_readAbove _ _ _ _ _ (by unfold ABI.paddedSize at *; omega)
      (by simp only [execGuardMiddleWords, List.length_cons, List.length_nil]; omega),
    execGuardHeadMemory, calldataBytesEncodedInto_read _ _ _ _ _ hin]

theorem execGuardArgsMemory_signatures (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (sender : UInt256) (sigLen : Nat) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size) (hn : words.length = (sigLen + 31) / 32) :
    (execGuardArgsMemory cd mem base src tx sender sigLen words).readWithPadding
      (base + 384 + ABI.paddedSize tx.payload.size) (32 + ABI.paddedSize sigLen) =
      (UInt256.ofNat sigLen).toByteArray ++ (wordBytes words).extract 0 sigLen ++
        ByteArray.zeroes (ABI.paddedSize sigLen - sigLen) := by
  have hp : ABI.paddedSize sigLen = 32 * words.length := by rw [hn]; rfl
  rw [execGuardArgsMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [memoryBytesEncodedInto_size _ _ _ _ hn]; unfold ABI.paddedSize; omega) (by omega),
    hp, memoryBytesEncodedInto_read _ _ _ _ hn]

theorem execGuardArgsMemory_read (cd mem : ByteArray) (base src : Nat)
    (tx : SafeTransaction) (sender : UInt256) (signatures : ByteArray) (words : List UInt256)
    (hin : src + tx.payload.size ≤ cd.size)
    (hd : cd.extract src (src + tx.payload.size) = tx.payload)
    (hn : words.length = (signatures.size + 31) / 32)
    (hp : (wordBytes words).extract 0 signatures.size = signatures) :
    (execGuardArgsMemory cd mem base src tx sender signatures.size words).readWithPadding
      base (416 + ABI.paddedSize tx.payload.size + ABI.paddedSize signatures.size) =
      execGuardArgsBytes tx signatures sender := by
  have hs := execGuardArgsMemory_size cd mem base src tx sender signatures.size words hin hn
  rw [show 416 + ABI.paddedSize tx.payload.size + ABI.paddedSize signatures.size =
      352 + ((32 + ABI.paddedSize tx.payload.size) + (32 + ABI.paddedSize signatures.size)) by
      omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by unfold ABI.paddedSize at *; omega),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by omega)
      (by unfold ABI.paddedSize at *; omega),
    show base + 352 + (32 + ABI.paddedSize tx.payload.size) =
      base + 384 + ABI.paddedSize tx.payload.size by omega,
    execGuardArgsMemory_static _ _ _ _ _ _ _ _ hin hn,
    execGuardArgsMemory_data _ _ _ _ _ _ _ _ hin hn,
    execGuardArgsMemory_signatures _ _ _ _ _ _ _ _ hin hn, hd, hp]
  simp only [execGuardArgsBytes, ByteArray.append_assoc]

end Benchmarks.Safe
