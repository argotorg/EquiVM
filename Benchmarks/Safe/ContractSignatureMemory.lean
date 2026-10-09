import Benchmarks.Safe.ContractSignatureSource
import Benchmarks.Safe.WordBytesEncoding
import Benchmarks.Safe.SelectorPatchMemory
import Benchmarks.Safe.PartialWordCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def contractSignatureCallLength (len : Nat) : Nat := 100 + ABI.paddedSize len

def contractSignatureCallEnd (ptr len : Nat) : Nat := ptr + 32 + contractSignatureCallLength len

def contractSignatureHeaderMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  writeWord (writeWord (wordBytesArgsMemory mem (ptr + 36) len hash words) ptr
    (UInt256.ofNat (contractSignatureCallLength len))) 64
    (UInt256.ofNat (contractSignatureCallEnd ptr len))

def contractSignatureEncodedMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  signatureMagicWord.toByteArray.write 0 (contractSignatureHeaderMemory mem ptr len hash words)
    (ptr + 32) 4

theorem contractSignatureHeaderMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureHeaderMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  simp only [contractSignatureHeaderMemory, writeWord_sparse_size,
    wordBytesArgsMemory_size _ _ _ _ _ hn]
  omega

theorem contractSignatureEncodedMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureEncodedMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  rw [contractSignatureEncodedMemory, copyWindow_size _ _ _ _ _ (by decide) (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega),
    contractSignatureHeaderMemory_size _ _ _ _ _ hn]
  omega

theorem contractSignatureEncodedMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureEncodedMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) := by
  apply memLoad_of_wordRead
  change (contractSignatureEncodedMemory mem ptr len hash words).readWithPadding 64 32 = _
  rw [contractSignatureEncodedMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega) (by omega)]
  exact writeWord_sparse_read_back _ _ _

theorem contractSignatureEncodedMemory_length (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    (contractSignatureEncodedMemory mem ptr len hash words).readWithPadding ptr 32 =
      (UInt256.ofNat (contractSignatureCallLength len)).toByteArray := by
  rw [contractSignatureEncodedMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega) (by omega),
    contractSignatureHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size]; omega) hp, writeWord_sparse_read_back]

theorem contractSignatureEncodedMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureEncodedMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureEncodedMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega) (by omega),
    contractSignatureHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size, wordBytesArgsMemory_size _ _ _ _ _ hn]; omega) hl,
    writeWordReadBelow _ _ _ _ _ (by
      rw [wordBytesArgsMemory_size _ _ _ _ _ hn]; omega) hh,
    wordBytesArgsMemory_preserved _ _ _ _ _ _ _ hin (by omega)]

theorem contractSignatureEncodedMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  have hsize := contractSignatureEncodedMemory_size mem ptr signature.size hash words hn
  have hsel : (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) 4 = isValidSignatureSelector := by
    rw [contractSignatureEncodedMemory, copySlice_read _ _ _ _ _ (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega)]
    decide +kernel
  have ht : (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 36) (96 + 32 * words.length) =
      wordBytes [hash, ⟨64⟩, UInt256.ofNat signature.size] ++ signature ++
        ByteArray.zeroes (32 * words.length - signature.size) := by
    rw [contractSignatureEncodedMemory, copyWindowReadAbove _ _ _ _ _ _ _ (by simp)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn]; omega)
      (by rw [contractSignatureHeaderMemory_size _ _ _ _ _ hn, hn]; omega) (by omega),
      contractSignatureHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
        rw [writeWord_sparse_size, wordBytesArgsMemory_size _ _ _ _ _ hn, hn]; omega)
        (by omega), writeWordReadAbove _ _ _ _ _ (by
        rw [wordBytesArgsMemory_size _ _ _ _ _ hn, hn]; omega) (by omega),
      wordBytesArgsMemory_read _ _ _ _ _ hn, hs]
  have hlen : contractSignatureCallLength signature.size = 4 + (96 + 32 * words.length) := by
    rw [contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  rw [hlen, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [hn] at *; omega), hsel, show ptr + 32 + 4 = ptr + 36 by omega, ht]
  simp only [contractSignatureCallBytes, ABI.paddedSize, hn, ByteArray.append_assoc]

def contractSignatureCallMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  forwardCopyMemory (contractSignatureEncodedMemory mem ptr len hash words) (ptr + 32)
    (contractSignatureCallEnd ptr len) (contractSignatureCallLength len)

theorem contractSignatureCallMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureCallMemory mem ptr len hash words).size =
      max mem.size (contractSignatureCallEnd ptr len + contractSignatureCallLength len + 32) := by
  rw [contractSignatureCallMemory, forwardCopyMemory_size _ _ _ _ (by
    dsimp [contractSignatureCallLength]; omega),
    contractSignatureEncodedMemory_size _ _ _ _ _ hn]
  simp only [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
  omega

theorem contractSignatureCallMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureCallMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) := by
  rw [contractSignatureCallMemory, memLoadReadWord,
    show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    forwardCopyMemory_preserved _ _ _ _ _ _ (by
      rw [contractSignatureEncodedMemory_size _ _ _ _ _ hn]; omega)
      (by dsimp [contractSignatureCallEnd]; omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord,
    contractSignatureEncodedMemory_free _ _ _ _ _ hn hp]

theorem contractSignatureCallMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureCallMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureCallMemory, forwardCopyMemory_preserved _ _ _ _ _ _ (by
    rw [contractSignatureEncodedMemory_size _ _ _ _ _ hn]; omega)
    (by dsimp [contractSignatureCallEnd]; omega),
    contractSignatureEncodedMemory_preserved _ _ _ _ _ _ _ hn hin hl hh]

theorem contractSignatureCallMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hb : ptr + 32 < UInt256.size)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureCallMemory mem ptr signature.size hash words).readWithPadding
      (contractSignatureCallEnd ptr signature.size) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  have hr := forwardCopyMemory_payload
    (contractSignatureEncodedMemory mem ptr signature.size hash words) (ptr + 32)
    (contractSignatureCallEnd ptr signature.size) (contractSignatureCallLength signature.size)
    (by dsimp [contractSignatureCallLength]; omega) (by
      rw [contractSignatureEncodedMemory_size _ _ _ _ _ hn]
      simp only [contractSignatureCallLength, ABI.paddedSize]
      omega) (le_refl _) hb
  exact hr.trans (contractSignatureEncodedMemory_read _ _ _ _ _ hn hp hs)

end Benchmarks.Safe
