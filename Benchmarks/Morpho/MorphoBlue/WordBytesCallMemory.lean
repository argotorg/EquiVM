import Benchmarks.Morpho.MorphoBlue.PaddedCopy
import Benchmarks.Morpho.MorphoBlue.WordBytesABI
import Benchmarks.Morpho.MorphoBlue.SafeTransferCallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: solc's ABI encoder for a word and calldata bytes.
def wordBytesCallMem (selector word : UInt256) (src mem : ByteArray) (srcOff off len : Nat) : ByteArray :=
  copyWithZeroWord src (staticWordCallMem selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off)
    srcOff (off + 100) len

theorem wordBytesCallMem_size (selector word : UInt256) (src mem : ByteArray) (srcOff off len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hg : off - mem.size < USize.size) :
    (wordBytesCallMem selector word src mem srcOff off len).size = max mem.size (off + 132 + len) := by
  have hb : (staticWordCallMem selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off).size =
      max mem.size (off + 100) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
      using staticWordCallMem_size selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off (by simp) hg
  rw [wordBytesCallMem, copyWithZeroWord_size _ _ _ _ _ hsrc (by rw [hb]; omega), hb]
  omega

theorem wordBytesCallMem_read (selector word : UInt256) (src mem data : ByteArray) (srcOff off len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hg : off - mem.size < USize.size)
    (hdata : src.readWithPadding srcOff len = data) (hlen : data.size = len) :
    (wordBytesCallMem selector word src mem srcOff off len).readWithPadding off (100 + paddedSize len) =
      wordBytesCalldata (selector.toByteArray.extract 0 4) word data := by
  let header := staticWordCallMem selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off
  have hb : header.size = max mem.size (off + 100) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
      using staticWordCallMem_size selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off (by simp) hg
  have hhead : (wordBytesCallMem selector word src mem srcOff off len).readWithPadding off 100 =
      selector.toByteArray.extract 0 4 ++ returnWordBytes [word, UInt256.ofNat 64, UInt256.ofNat len] := by
    rw [wordBytesCallMem, copyWithZeroWord_preserve _ _ _ _ _ _ _ hsrc (by exact (hb ▸ Nat.le_max_right _ _)) (by omega)]
    exact staticWordCallMem_read selector _ mem off (by simp) hg
  have hl := nat_le_paddedSize len
  have hp := paddedSize_le_add31 len
  have htail := copyWithZeroWord_read src header srcOff (off + 100) len (paddedSize len - len)
    hsrc (by rw [hb]; omega) (by omega)
  rw [show len + (paddedSize len - len) = paddedSize len by omega, hdata] at htail
  by_cases hz : paddedSize len = 0
  · have hzlen : len = 0 := by omega
    have hzd : data = ByteArray.empty := by
      have hzr := byteArray_readWithPadding_zero src srcOff
      rw [hzlen] at hdata
      exact hdata.symm.trans hzr
    simp only [hz, Nat.add_zero]
    rw [hhead, wordBytesCalldata, wordBytesArguments, hlen, hzlen, hzd]
    simp only [show paddedSize 0 = 0 from rfl, Nat.sub_self, zeroes_zero (n := 0) rfl, ByteArray.append_empty]
  · rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [wordBytesCallMem_size selector word src mem srcOff off len hsrc hg]; omega), hhead]
    change _ ++ (copyWithZeroWord src header srcOff (off + 100) len).readWithPadding _ _ = _
    rw [htail, wordBytesCalldata, wordBytesArguments, hlen]
    simp only [ByteArray.append_assoc]

theorem wordBytesCallMem_read_below (selector word : UInt256) (src mem : ByteArray)
    (srcOff off len read : Nat) (hsrc : srcOff + len ≤ src.size) (hg : off - mem.size < USize.size)
    (hin : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ off) :
    (wordBytesCallMem selector word src mem srcOff off len).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hs := writeWord_size mem off selector hg
  have hg' : off + 4 - (writeWord mem off selector).size < USize.size := by
    rw [hs]; have hu := USize.size_pos; omega
  have hb : (staticWordCallMem selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off).size =
      max mem.size (off + 100) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
      using staticWordCallMem_size selector [word, UInt256.ofNat 64, UInt256.ofNat len] mem off (by simp) hg
  rw [wordBytesCallMem, copyWithZeroWord_preserve _ _ _ _ _ _ _ hsrc (by rw [hb]; omega) (by omega)]
  unfold staticWordCallMem
  rw [writeCascade_read_preserved _ _ _
      (returnWordWrites_preserveBelow _ _ _ _ _ hg' (by rw [hs]; omega) (by omega)),
    writeWord_read_preserved _ _ _ _ hg (Or.inl ⟨hbelow, hin⟩)]

theorem wordBytesCallMem_load_below (selector word : UInt256) (src mem : ByteArray)
    (srcOff off len : Nat) (read : UInt256) (hsrc : srcOff + len ≤ src.size)
    (hg : off - mem.size < USize.size) (hin : read.toNat + 32 ≤ mem.size)
    (hbelow : read.toNat + 32 ≤ off) :
    memLoad read (wordBytesCallMem selector word src mem srcOff off len) = memLoad read mem := by
  have hs := wordBytesCallMem_size selector word src mem srcOff off len hsrc hg
  unfold memLoad
  rw [if_neg (show ¬ read.toNat ≥ (wordBytesCallMem selector word src mem srcOff off len).size by rw [hs]; omega),
    if_neg (show ¬ read.toNat ≥ mem.size by omega),
    wordBytesCallMem_read_below selector word src mem srcOff off len read.toNat hsrc hg hin hbelow]

theorem wordBytesCallMem_prefix (selector word : UInt256) (src mem : ByteArray)
    (srcOff off len : Nat) (hsrc : srcOff + len ≤ src.size) (hg : off - mem.size < USize.size) :
    MemoryPrefix mem (wordBytesCallMem selector word src mem srcOff off len) off := by
  refine ⟨?_, fun read _ hbelow hin =>
    wordBytesCallMem_read_below selector word src mem srcOff off len read hsrc hg hin hbelow⟩
  rw [wordBytesCallMem_size selector word src mem srcOff off len hsrc hg]
  exact Nat.le_max_left _ _

theorem MorphoHeap.wordBytesCall {mem : ByteArray} {ptr : UInt256}
    (hm : MorphoHeap mem ptr 0) (selector word : UInt256) (src : ByteArray) (srcOff len : Nat)
    (hsrc : srcOff + len ≤ src.size) :
    MorphoHeap (wordBytesCallMem selector word src mem srcOff ptr.toNat len) ptr 0 := by
  have hg : ptr.toNat - mem.size < USize.size := by have hh := hm.gap; omega
  have hs := wordBytesCallMem_size selector word src mem srcOff ptr.toNat len hsrc hg
  refine ⟨by rw [hs]; have hh := hm.size; omega, ?_, hm.lower,
    by rw [hs]; have hh := hm.gap; omega, hm.space⟩
  rw [wordBytesCallMem_load_below _ _ _ _ _ _ _ (UInt256.ofNat 64) hsrc hg hm.size hm.lower, hm.free]

end Benchmarks.Morpho.MorphoBlue
