import Benchmarks.CompoundIII.Comet.AssetSource
import Benchmarks.CompoundIII.Comet.CallWordMemory
import Benchmarks.CompoundIII.Comet.AssetStructMemory
import Benchmarks.CompoundIII.Comet.PriceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def assetSelectorWord : UInt256 := UInt256.shiftLeft ⟨3368549995⟩ ⟨224⟩

def assetInputMemory (mem : ByteArray) (ptr i : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat assetSelectorWord) (ptr + UInt256.ofNat 4).toNat i

theorem assetInputMemory_size {mem : ByteArray} {ptr i : UInt256}
    (hb : ptr.toNat + 36 < UInt256.size) :
    (assetInputMemory mem ptr i).size = max mem.size (ptr.toNat + 36) := by
  exact callWordMemory_size hb

theorem assetInputMemory_payload {mem : ByteArray} {ptr i : UInt256}
    (hb : ptr.toNat + 36 < UInt256.size) :
    (assetInputMemory mem ptr i).readWithPadding ptr.toNat 36 = assetPayload i := by
  have hr := callWordMemory_payload (mem := mem) (ptr := ptr)
    (selector := assetSelectorWord) (arg := i) hb
  have hsel : assetSelectorWord.toByteArray.extract 0 4 =
      ByteArray.mk #[200, 199, 254, 107] := by decide +kernel
  rw [hsel, toByteArray_eq_toBytesBE] at hr
  exact hr.trans (by
    apply ByteArray.ext
    simp only [ByteArray.data_append, assetPayload, List.append_toArray])

-- LIBRARY CANDIDATE: loading the word just stored, with memory growth handled by the library.
theorem memLoad_writeWord_self (mem : ByteArray) (ptr word : UInt256) :
    memLoad ptr (writeWord mem ptr.toNat word) = word :=
  loadedWord_of_read (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _)
    (writeWord_sparse_read_back _ _ _)

def assetCopyMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  callOutputMem mem out ptr ⟨256⟩

def assetReserveMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (assetCopyMemory mem ptr out) 64 (ptr + ⟨256⟩)

def assetDecodeMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (assetReserveMemory mem ptr out) 64 ((ptr + ⟨256⟩) + ⟨256⟩)

theorem assetCopyMemory_size {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (assetCopyMemory mem ptr out).size = max mem.size (ptr.toNat + 256) := by
  have hl : (min (⟨256⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 256 :=
    umin_ofNat_right_toNat_of_ge (c := 256) (n := out.size) (by decide) hout hhi
  rw [assetCopyMemory, callOutputMem, hl, writePrefix_size _ _ _ _ (by decide) hout hin]

theorem assetReserveMemory_size {mem out : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (assetReserveMemory mem ptr out).size = max mem.size (ptr.toNat + 256) := by
  rw [assetReserveMemory, writeWord_sparse_size, assetCopyMemory_size hin hout hhi]
  omega

theorem assetDecodeMemory_size {mem out : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hout : 256 ≤ out.size) (hhi : out.size < UInt256.size) :
    (assetDecodeMemory mem ptr out).size = max mem.size (ptr.toNat + 256) := by
  rw [assetDecodeMemory, writeWord_sparse_size, assetReserveMemory_size hlo hin hout hhi]
  omega

theorem assetReserveMemory_free (mem out : ByteArray) (ptr : UInt256) :
    memLoad ⟨64⟩ (assetReserveMemory mem ptr out) = ptr + ⟨256⟩ :=
  memLoad_writeWord_self _ ⟨64⟩ _

theorem assetDecodeMemory_free (mem out : ByteArray) (ptr : UInt256) :
    memLoad ⟨64⟩ (assetDecodeMemory mem ptr out) = (ptr + ⟨256⟩) + ⟨256⟩ :=
  memLoad_writeWord_self _ ⟨64⟩ _

theorem assetCopyMemory_word {mem out : ByteArray} {ptr : UInt256} (off : Nat)
    (hoff : off ≤ 224) (hin : ptr.toNat ≤ mem.size)
    (hptr : ptr.toNat + 256 < UInt256.size) (hout : 256 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    memLoad (ptr + UInt256.ofNat off) (assetCopyMemory mem ptr out) =
      calldataWord out off := by
  have ha := uadd_word_ofNat_toNat ptr off (by omega)
  apply loadedWord_of_read
  · rw [ha, assetCopyMemory_size hin hout hhi]; omega
  · rw [ha]
    unfold assetCopyMemory callOutputMem
    have hl : (min (⟨256⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 256 :=
      umin_ofNat_right_toNat_of_ge (c := 256) (n := out.size) (by decide) hout hhi
    rw [hl, writeReturnCopy_read32 out mem ptr.toNat 256 (ptr.toNat + off) hout
      hin (by omega) (by omega), show ptr.toNat + off - ptr.toNat = off by omega]
    exact (calldataWord_bytes_at (by omega)).symm

theorem assetDecodeMemory_word {mem out : ByteArray} {ptr : UInt256} (off : Nat)
    (hoff : off ≤ 224) (hlo : 96 ≤ ptr.toNat) (hin : ptr.toNat ≤ mem.size)
    (hptr : ptr.toNat + 256 < UInt256.size) (hout : 256 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    memLoad (ptr + UInt256.ofNat off) (assetDecodeMemory mem ptr out) =
      calldataWord out off := by
  have hp : MemoryPrefix (assetCopyMemory mem ptr out) (assetDecodeMemory mem ptr out)
      (ptr.toNat + 256) :=
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide)))
  have ha := uadd_word_ofNat_toNat ptr off (by omega)
  rw [memoryPrefix_load hp (by rw [ha]; omega) (by rw [ha]; omega)
    (by rw [ha, assetCopyMemory_size hin hout hhi]; omega)]
  exact assetCopyMemory_word off hoff hin hptr hout hhi

end Benchmarks.CompoundIII.Comet
