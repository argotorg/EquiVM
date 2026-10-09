import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.Memory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def addressArrayHeaderMemory (mem : ByteArray) (ptr count : Nat) : ByteArray :=
  writeWord (writeWord mem ptr ⟨32⟩) (ptr + 32) (UInt256.ofNat count)

def addressArrayReturnBytes (words : List UInt256) : ByteArray :=
  wordBytes (⟨32⟩ :: UInt256.ofNat words.length :: words)

theorem addressArrayHeaderSize (mem : ByteArray) (ptr count : Nat) (hm : mem.size ≤ ptr) :
    (addressArrayHeaderMemory mem ptr count).size = ptr + 64 := by
  simp only [addressArrayHeaderMemory, writeWord_sparse_size]
  omega

theorem addressArrayHeaderWords (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (src : Nat) (hw : WordArrayMemory mem src words) (hm : mem.size % 32 = 0)
    (hs : src % 32 = 0) (hp : ptr % 32 = 0) (hafter : src + 32 * words.length ≤ ptr)
    (count : Nat := words.length) :
    WordArrayMemory (addressArrayHeaderMemory mem ptr count) src words := by
  exact (hw.writeDisjoint mem src words hm hs ptr ⟨32⟩ (.inr hafter)).writeDisjoint
    _ src words (writeWord_size_aligned _ _ _ hm hp) hs (ptr + 32)
    (UInt256.ofNat count) (.inr (by omega))

theorem addressArrayHeaderRead (mem : ByteArray) (ptr count read : Nat)
    (hin : read + 32 ≤ mem.size) (hbefore : read + 32 ≤ ptr) :
    (addressArrayHeaderMemory mem ptr count).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [addressArrayHeaderMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hbefore, hin⟩)]

-- GENERALIZES the appended-tail memory read to unrestricted return lengths.
theorem readAppendTail (before after : ByteArray) :
    (before ++ after).readWithPadding before.size after.size = after := by
  by_cases hz : after.size = 0
  · rw [hz, byteArray_readWithPadding_zero]
    exact (byteArray_eq_empty_of_size_eq_zero _ hz).symm
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
      (by rw [ByteArray.size_append]), extract_append_right]

-- LIBRARY CANDIDATE: an in-bounds read in a prefix is unchanged by an append.
theorem readAppendPrefixLen (before after : ByteArray) (off len : Nat)
    (hin : off + len ≤ before.size) :
    (before ++ after).readWithPadding off len = before.readWithPadding off len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
      (by rw [ByteArray.size_append]; omega), extract_append_left _ _ _ _ hin,
      ← readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin]

theorem readAppendPrefix (before after : ByteArray) (off : Nat)
    (hin : off + 32 ≤ before.size) :
    (before ++ after).readWithPadding off 32 = before.readWithPadding off 32 :=
  readAppendPrefixLen before after off 32 hin

-- LIBRARY CANDIDATE: serialized words appended to a buffer form a memory array.
theorem WordArrayMemory.appendBytes (mem : ByteArray) (words : List UInt256) :
    WordArrayMemory (mem ++ wordBytes words) mem.size words := by
  induction words generalizing mem with
  | nil => intro i hi; simp at hi
  | cons w ws ih =>
      rw [wordBytes, ← ByteArray.append_assoc]
      apply WordArrayMemory.cons
      · rw [readAppendPrefix _ _ _ (by rw [ByteArray.size_append, toByteArray_size])]
        simpa only [toByteArray_size] using readAppendTail mem w.toByteArray
      · simpa only [ByteArray.size_append, toByteArray_size] using ih (mem ++ w.toByteArray)

-- LIBRARY CANDIDATE: the same two-word ABI header supports arrays and byte buffers.
theorem wordBufferEncodedRead (mem : ByteArray) (ptr count : Nat) (words : List UInt256)
    (hm : mem.size ≤ ptr) :
    (addressArrayHeaderMemory mem ptr count ++ wordBytes words).readWithPadding ptr
      (64 + 32 * words.length) = wordBytes (⟨32⟩ :: UInt256.ofNat count :: words) := by
  have hs : (writeWord mem ptr (⟨32⟩ : UInt256)).size = ptr + 32 := by
    rw [writeWord_sparse_size, Nat.max_eq_right (by omega)]
  have hp : (mem ++ ByteArray.zeroes (ptr - mem.size)).size = ptr := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  have hsize : (wordBytes (⟨32⟩ :: UInt256.ofNat count :: words)).size =
      64 + 32 * words.length := by
    simp only [wordBytes_size, List.length_cons]
    omega
  rw [addressArrayHeaderMemory,
    show writeWord (writeWord mem ptr ⟨32⟩) (ptr + 32) (UInt256.ofNat count) =
      writeWord mem ptr ⟨32⟩ ++ (UInt256.ofNat count).toByteArray from
      writeWordAtEnd _ _ hs,
    writeWord_sparse_eq mem ptr ⟨32⟩ hm, ByteArray.append_assoc, ByteArray.append_assoc]
  change ((mem ++ ByteArray.zeroes (ptr - mem.size)) ++
    wordBytes (⟨32⟩ :: UInt256.ofNat count :: words)).readWithPadding ptr
      (64 + 32 * words.length) = _
  simpa only [hp, hsize] using
    readAppendTail (mem ++ ByteArray.zeroes (ptr - mem.size))
      (wordBytes (⟨32⟩ :: UInt256.ofNat count :: words))

theorem addressArrayEncodedRead (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (hm : mem.size ≤ ptr) :
    (addressArrayHeaderMemory mem ptr words.length ++ wordBytes words).readWithPadding ptr
      (64 + 32 * words.length) = addressArrayReturnBytes words :=
  wordBufferEncodedRead mem ptr words.length words hm

-- LIBRARY CANDIDATE: canonical address words have their ordinary word encoding.
theorem addressArrayElemsEncoding (words : List UInt256)
    (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus) :
    encodeABIStaticArrayElems? (.elem .address)
      (words.map (fun w ↦ Value.address (AccountAddress.ofNat w.toNat))) =
      some (words.flatMap EVM.Word.toBytesBE) := by  induction words with
  | nil => simp [encodeABIStaticArrayElems?]
  | cons w ws ih =>
      have hw := encodeABIValue_address_word w
      rw [solcAddrMask_clean (hc w (by simp))] at hw
      rw [← word_toBytesBE_eq_toByteArray_toList] at hw
      simp only [List.map_cons, List.flatMap_cons, encodeABIStaticArrayElems?, hw,
        ih (fun v hv ↦ hc v (by simp [hv])), bind, Option.bind, pure]

-- LIBRARY CANDIDATE: canonical EVM words encode as a dynamic ABI address array.
theorem addressArrayReturnEncoding (words : List UInt256)
    (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus) :
    encodeReturnValues? [.dynamicArray (.elem .address)]
      [.array (words.map (fun w ↦ Value.address (AccountAddress.ofNat w.toNat)))] =
      some (addressArrayReturnBytes words) := by
  have hvalues := addressArrayElemsEncoding words hc
  unfold encodeReturnValues?
  rw [encodeABIValues_single_dynArray_static (by rfl), hvalues]
  simp only [List.length_map, bind, Option.bind, pure, byteArray_mk_toArray_eq_toByteArray]
  rw [addressArrayReturnBytes, wordBytes_eq_list]
  rfl

end Benchmarks.Safe
