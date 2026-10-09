import Benchmarks.Safe.WordArrayMemory
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

def addressArrayFreePtr (n : Nat) : UInt256 := UInt256.ofNat (160 + 32 * n)

def wordBufferAllocatedMemory (mem : ByteArray) (n : Nat) (header : UInt256) : ByteArray :=
  writeWord (writeWord mem 128 header) 64 (addressArrayFreePtr n)

def addressArrayAllocatedMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  wordBufferAllocatedMemory mem n (UInt256.ofNat n)

-- A byte buffer and an address array share this layout; their length headers differ.
structure AddressArrayMemory (mem : ByteArray) (n : Nat) (words : List UInt256)
    (header : UInt256 := UInt256.ofNat n) : Prop where
  length : words.length = n
  aligned : mem.size % 32 = 0
  lower : 160 ≤ mem.size
  upper : mem.size ≤ 160 + 32 * n
  freePtr : mem.readWithPadding 64 32 = (addressArrayFreePtr n).toByteArray
  count : mem.readWithPadding 128 32 = header.toByteArray
  words : WordArrayMemory mem 160 words

theorem safeWordBufferAllocatedSize (mem : ByteArray) (n : Nat) (header : UInt256)
    (hm : mem.size = 96) : (wordBufferAllocatedMemory mem n header).size = 160 := by
  simp only [wordBufferAllocatedMemory, writeWord_sparse_size, hm]
  decide +kernel

theorem safeWordBufferAllocated (mem : ByteArray) (n : Nat) (header : UInt256)
    (hm : mem.size = 96) :
    AddressArrayMemory (wordBufferAllocatedMemory mem n header) n
      (List.replicate n ⟨0⟩) header := by
  have hs := safeWordBufferAllocatedSize mem n header hm
  refine ⟨List.length_replicate, by rw [hs], by omega, by omega, ?_, ?_, ?_⟩
  · exact writeWord_sparse_read_back _ _ _
  · change (writeWord (writeWord mem 128 header) 64
      (addressArrayFreePtr n)).readWithPadding 128 32 = _
    rw [writeWord_read_disjoint_padded _ _ _ _
      (.inl (by rw [writeWord_sparse_size, hm]; decide)) (.inr (by decide))]
    exact writeWord_sparse_read_back _ _ _
  · exact WordArrayMemory.zeroes _ _ _ (by omega)

theorem safeAddressArrayAllocatedSize (mem : ByteArray) (n : Nat) (hm : mem.size = 96) :
    (addressArrayAllocatedMemory mem n).size = 160 :=
  safeWordBufferAllocatedSize mem n _ hm

theorem safeAddressArrayAllocated (mem : ByteArray) (n : Nat) (hm : mem.size = 96) :
    AddressArrayMemory (addressArrayAllocatedMemory mem n) n (List.replicate n ⟨0⟩) :=
  safeWordBufferAllocated mem n _ hm

theorem AddressArrayMemory.scratch {mem n words header}
    (h : AddressArrayMemory mem n words header) (key slot : UInt256) :
    AddressArrayMemory (twoWordHashMem key slot mem) n words header := by
  have hs := twoWordHashMem_size_of_ge_64' (mem := mem) key slot (by have := h.lower; omega)
  refine ⟨h.length, by rw [hs]; exact h.aligned, by rw [hs]; exact h.lower,
    by rw [hs]; exact h.upper, ?_, ?_, ?_⟩
  · rw [twoWordHashMem_read_above64 key slot 64 (by decide) (by have := h.lower; omega)]
    exact h.freePtr
  · rw [twoWordHashMem_read_above64 key slot 128 (by decide) h.lower]
    exact h.count
  · exact h.words.scratch mem 160 words (by have := h.lower; omega) h.aligned
      (by decide) (by decide) key slot

theorem AddressArrayMemory.write {mem n words header} (h : AddressArrayMemory mem n words header)
    (i : Nat) (value : UInt256) (hi : i < n) :
    AddressArrayMemory (writeWord mem (160 + 32 * i) value) n (words.set i value) header := by
  have hi' : i < words.length := by rw [h.length]; exact hi
  refine ⟨by simpa using h.length, writeWord_size_aligned _ _ _ h.aligned (by omega),
    ?_, ?_, ?_, ?_, h.words.write mem 160 words h.aligned (by decide) i value hi'⟩
  · rw [writeWord_sparse_size]
    have := h.lower
    omega
  · rw [writeWord_sparse_size]
    have := h.upper
    omega
  · rw [writeWord_read_disjoint_padded _ _ _ _ (.inl (by have := h.lower; omega))
      (.inl (by omega))]
    exact h.freePtr
  · rw [writeWord_read_disjoint_padded _ _ _ _ (.inl h.lower) (.inl (by omega))]
    exact h.count

theorem safeAddressArrayIndexAddress (i : Nat) (hi : i ≤ 2 ^ 64 - 1) :
    (UInt256.ofNat 32 + (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i) +
      UInt256.ofNat 128)).toNat = 160 + 32 * i := by
  have hib : i < UInt256.size := by change i < 2 ^ 256; omega
  have hw := ulit_toNat' i hib
  have hp : (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)).toNat = 32 * i := by
    change (32 * (UInt256.ofNat i).toNat) % UInt256.size = _
    rw [hw]
    exact Nat.mod_eq_of_lt (by change 32 * i < 2 ^ 256; omega)
  rw [uadd_toNat, uadd_toNat, hp]
  change (32 + (32 * i + 128) % UInt256.size) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (show 32 * i + 128 < UInt256.size by
    change 32 * i + 128 < 2 ^ 256; omega)]
  rw [Nat.mod_eq_of_lt (by change 32 + (32 * i + 128) < 2 ^ 256; omega)]
  omega

theorem addressArrayFreePtr_eq (n : Nat) (hn : n ≤ 2 ^ 64 - 1) :
    (⟨128⟩ : UInt256) + (UInt256.ofNat 32 +
      UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)) = addressArrayFreePtr n := by
  apply u256_inj
  rw [u256_add_comm (⟨128⟩ : UInt256) _, uadd_assoc]
  change (UInt256.ofNat 32 + (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n) +
    UInt256.ofNat 128)).toNat = _
  rw [safeAddressArrayIndexAddress n hn]
  exact (ulit_toNat' _ (by change 160 + 32 * n < 2 ^ 256; omega)).symm

-- LIBRARY CANDIDATE: rounding an already word-aligned byte length does not change it.
theorem wordAlignedRoundUp (n : Nat) (hn : n + 31 < UInt256.size) (ha : n % 32 = 0) :
    UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat 31 + UInt256.ofNat n) = UInt256.ofNat n := by
  apply u256_inj
  rw [u256_land_comm]
  change (UInt256.land (UInt256.ofNat 31 + UInt256.ofNat n) (UInt256.lnot ⟨31⟩)).toNat = _
  rw [longDataCutoff_toNat, uadd_toNat, ulit_toNat' n (by omega)]
  change (((31 + n) % UInt256.size) / 32) * 32 = n
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end Benchmarks.Safe
