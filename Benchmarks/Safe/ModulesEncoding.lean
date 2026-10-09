import Benchmarks.Safe.AddressArrayEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def modulesHeaderMemory (mem : ByteArray) (ptr count : Nat) : ByteArray :=
  writeWord (writeWord mem ptr ⟨64⟩) (ptr + 64) (UInt256.ofNat count)

def modulesEncodedMemory (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (next : UInt256) : ByteArray :=
  writeWord (modulesHeaderMemory mem ptr words.length ++ wordBytes words) (ptr + 32) next

def modulesReturnBytes (words : List UInt256) (next : UInt256) : ByteArray :=
  wordBytes (⟨64⟩ :: next :: UInt256.ofNat words.length :: words)

theorem modulesHeaderSize (mem : ByteArray) (ptr count : Nat) (hm : mem.size ≤ ptr) :
    (modulesHeaderMemory mem ptr count).size = ptr + 96 := by
  simp only [modulesHeaderMemory, writeWord_sparse_size]
  omega

theorem modulesHeaderWords (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (hw : WordArrayMemory mem 160 words) (hm : mem.size % 32 = 0)
    (hp : ptr % 32 = 0) (hafter : 160 + 32 * words.length ≤ ptr) :
    WordArrayMemory (modulesHeaderMemory mem ptr words.length) 160 words := by
  exact (hw.writeDisjoint mem 160 words hm (by decide) ptr ⟨64⟩ (.inr hafter)).writeDisjoint
    _ 160 words (writeWord_size_aligned _ _ _ hm hp) (by decide) (ptr + 64)
    (UInt256.ofNat words.length) (.inr (by omega))

theorem modulesHeaderRead (mem : ByteArray) (ptr count read : Nat)
    (hin : read + 32 ≤ mem.size) (hbefore : read + 32 ≤ ptr) :
    (modulesHeaderMemory mem ptr count).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  rw [modulesHeaderMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hbefore, hin⟩)]

theorem modulesEncodedSize (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (next : UInt256) (hm : mem.size ≤ ptr) :
    (modulesEncodedMemory mem ptr words next).size = ptr + 96 + 32 * words.length := by
  rw [modulesEncodedMemory, writeWord_sparse_size, ByteArray.size_append,
    modulesHeaderSize _ _ _ hm, wordBytes_size, Nat.max_eq_left (by omega)]

theorem modulesEncodedRead (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (next : UInt256) (hm : mem.size ≤ ptr) :
    (modulesEncodedMemory mem ptr words next).readWithPadding ptr (96 + 32 * words.length) =
      modulesReturnBytes words next := by
  let headMem := modulesHeaderMemory mem ptr words.length
  have hh : headMem.size = ptr + 96 := modulesHeaderSize _ _ _ hm
  have hsize : (headMem ++ wordBytes words).size = ptr + 96 + 32 * words.length := by
    rw [ByteArray.size_append, hh, wordBytes_size]
  have h0 : (modulesEncodedMemory mem ptr words next).readWithPadding ptr 32 =
      (⟨64⟩ : UInt256).toByteArray := by
    rw [modulesEncodedMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by change ptr + 32 ≤ (headMem ++ wordBytes words).size; omega⟩),
      readAppendPrefix _ _ _ (by rw [modulesHeaderSize _ _ _ hm]; omega),
      modulesHeaderMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]
  have h1 : (modulesEncodedMemory mem ptr words next).readWithPadding (ptr + 32) 32 =
      next.toByteArray := writeWord_sparse_read_back _ _ _
  have h2 : (modulesEncodedMemory mem ptr words next).readWithPadding (ptr + 64) 32 =
      (UInt256.ofNat words.length).toByteArray := by
    rw [modulesEncodedMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inr ⟨by omega, by change ptr + 64 + 32 ≤ (headMem ++ wordBytes words).size; omega⟩),
      readAppendPrefix _ _ _ (by rw [modulesHeaderSize _ _ _ hm]),
      modulesHeaderMemory, writeWord_sparse_read_back]
  have hw := (WordArrayMemory.appendBytes headMem words).writeBefore
    (headMem ++ wordBytes words) headMem.size words
    (by rw [ByteArray.size_append, wordBytes_size]) (ptr + 32) next (by omega)
  rw [hh] at hw
  have hall : WordArrayMemory (modulesEncodedMemory mem ptr words next) ptr
      (⟨64⟩ :: next :: UInt256.ofNat words.length :: words) :=
    .cons h0 (.cons h1 (.cons (by simpa [Nat.add_assoc] using h2)
      (by simpa [Nat.add_assoc] using hw)))
  have hr := hall.read _ _ _ (by rw [modulesEncodedSize _ _ _ _ hm]; simp; omega)
  have hlen : 32 * (words.length + 1 + 1 + 1) = 96 + 32 * words.length := by omega
  simpa only [List.length_cons, hlen, modulesReturnBytes] using hr

theorem modulesEncodedRead64 (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (next : UInt256) (hm : mem.size ≤ ptr) (hmem : 96 ≤ mem.size) :
    (modulesEncodedMemory mem ptr words next).readWithPadding 64 32 = mem.readWithPadding 64 32 :=
      by
  rw [modulesEncodedMemory, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [ByteArray.size_append, modulesHeaderSize _ _ _ hm]; omega⟩),
    readAppendPrefix _ _ _ (by rw [modulesHeaderSize _ _ _ hm]; omega),
    modulesHeaderRead _ _ _ _ hmem (by omega)]

theorem modulesReturnEncoding (words : List UInt256) (next : UInt256)
    (hc : ∀ w ∈ words, w.toNat < EVM.addressModulus)
    (hn : next.toNat < EVM.addressModulus) :
    encodeReturnValues? [.dynamicArray (.elem .address), .elem .address]
      [.array (words.map (fun w ↦ Value.address (AccountAddress.ofNat w.toNat))),
        .address (AccountAddress.ofNat next.toNat)] = some (modulesReturnBytes words next) := by
  have hw := addressArrayElemsEncoding words hc
  have hnext := encodeABIValue_address_word next
  rw [solcAddrMask_clean hn, ← word_toBytesBE_eq_toByteArray_toList] at hnext
  have harray : encodeABIValue? (.dynamicArray (.elem .address))
      (.array (words.map (fun w ↦ Value.address (AccountAddress.ofNat w.toNat)))) =
      some (natBytes words.length ++ words.flatMap EVM.Word.toBytesBE) := by
    simp [encodeABIValue?, encodeABIArrayElems?, isDynamicABIType, hw]
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, harray, hnext, bind, Option.bind, pure,
    List.length_nil, Nat.add_zero, List.nil_append]
  rw [modulesReturnBytes, wordBytes_eq_list]
  simp only [List.flatMap_cons, byteArray_mk_toArray_eq_toByteArray, List.append_assoc]
  rfl

end Benchmarks.Safe
