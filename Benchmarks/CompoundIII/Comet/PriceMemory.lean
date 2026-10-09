import Benchmarks.CompoundIII.Comet.PriceSource
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def priceSelectorWord : UInt256 := UInt256.shiftLeft ⟨1068230051⟩ ⟨226⟩

def priceInputMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord mem ptr.toNat priceSelectorWord

def priceCopyMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  callOutputMem (priceInputMemory mem ptr) out ptr ⟨160⟩

def priceReturnMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (priceCopyMemory mem ptr out) 64 (ptr + ⟨160⟩)

theorem priceInputMemory_payload {mem : ByteArray} {ptr : UInt256}
    (hgap : ptr.toNat ≤ mem.size + 32) :
    (priceInputMemory mem ptr).readWithPadding ptr.toNat 4 = pricePayload := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hh := lt_usize 32 (by decide)
    omega
  have hr := toByteArray_write_read_window_of_gap priceSelectorWord mem ptr.toNat 0 4
    (by decide) (by decide) (by decide) hg
  have hsel : priceSelectorWord.toByteArray.extract 0 (0 + 4) = pricePayload := by
    decide +kernel
  simpa only [Nat.add_zero] using hr.trans hsel

-- LIBRARY CANDIDATE: size of a bounded source-prefix write without a destination gap.
theorem writePrefix_size (src mem : ByteArray) (off len : Nat)
    (hpos : len ≠ 0) (hlen : len ≤ src.size) (hin : off ≤ mem.size) :
    (src.write 0 mem off len).size = max mem.size (off + len) := by
  by_cases he : off + len ≤ mem.size
  · rw [write_eq_gen src mem off len hpos hlen he]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega
  · rw [write_eq_gen_extend src mem off len hpos hlen hin (by omega)]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    omega

theorem priceCopyMemory_size {mem out : ByteArray} {ptr : UInt256}
    (hgap : ptr.toNat ≤ mem.size + 32) (hout : 160 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    (priceCopyMemory mem ptr out).size = max mem.size (ptr.toNat + 160) := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hh := lt_usize 32 (by decide)
    omega
  have hs := writeWord_size mem ptr.toNat priceSelectorWord hg
  have hl : (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
    umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hout hhi
  unfold priceCopyMemory callOutputMem
  rw [hl]
  rw [writePrefix_size _ _ _ _ (by decide) hout (by
    change ptr.toNat ≤ (writeWord mem ptr.toNat priceSelectorWord).size
    rw [hs]; omega)]
  change max (writeWord mem ptr.toNat priceSelectorWord).size (ptr.toNat + 160) = _
  rw [hs]
  omega

theorem priceReturnMemory_size {mem out : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat ≤ mem.size + 32) (hout : 160 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    (priceReturnMemory mem ptr out).size = max mem.size (ptr.toNat + 160) := by
  have hs := priceCopyMemory_size hgap hout hhi
  unfold priceReturnMemory
  rw [writeWord_size _ _ _ (by
    rw [hs]
    exact lt_of_le_of_lt (by omega) (lt_usize 0 (by decide)))]
  rw [hs]
  omega

theorem priceReturnMemory_free {mem out : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat ≤ mem.size + 32) (hout : 160 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    memLoad ⟨64⟩ (priceReturnMemory mem ptr out) = ptr + ⟨160⟩ := by
  apply loadedWord_of_read
  · rw [priceReturnMemory_size hlo hgap hout hhi]
    change 64 + 32 ≤ _
    omega
  · exact writeWord_read_back _ 64 _ (by
      rw [priceCopyMemory_size hgap hout hhi]
      exact lt_of_le_of_lt (by omega) (lt_usize 0 (by decide)))

theorem priceReturnMemory_word {mem out : ByteArray} {ptr : UInt256} (off : Nat)
    (hoff : off ≤ 128) (hlo : 96 ≤ ptr.toNat) (hgap : ptr.toNat ≤ mem.size + 32)
    (hptr : ptr.toNat + 160 < 2^64) (hout : 160 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    memLoad (ptr + UInt256.ofNat off) (priceReturnMemory mem ptr out) =
      calldataWord out off := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hh := lt_usize 32 (by decide)
    omega
  have hinput := writeWord_size mem ptr.toNat priceSelectorWord hg
  have hcopy := priceCopyMemory_size hgap hout hhi
  have hret := priceReturnMemory_size hlo hgap hout hhi
  have haddr : (ptr + UInt256.ofNat off).toNat = ptr.toNat + off := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by change off < 2^256; omega)]
    exact Nat.mod_eq_of_lt (by change ptr.toNat + off < 2^256; omega)
  apply loadedWord_of_read
  · rw [haddr, hret]; omega
  · rw [haddr]
    rw [show (priceReturnMemory mem ptr out).readWithPadding (ptr.toNat + off) 32 =
        (priceCopyMemory mem ptr out).readWithPadding (ptr.toNat + off) 32 from
      writeWord_read_preserved _ 64 _ _
        (lt_of_le_of_lt (by rw [hcopy]; omega) (lt_usize 0 (by decide)))
        (Or.inr ⟨by omega, by rw [hcopy]; omega⟩)]
    unfold priceCopyMemory callOutputMem
    have hl : (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 :=
      umin_ofNat_right_toNat_of_ge (c := 160) (n := out.size) (by decide) hout hhi
    rw [hl]
    rw [writeReturnCopy_read32 out _ ptr.toNat 160 (ptr.toNat + off) hout
      (by change ptr.toNat ≤ (writeWord mem ptr.toNat priceSelectorWord).size
          rw [hinput]; omega) (by omega) (by omega)]
    rw [show ptr.toNat + off - ptr.toNat = off by omega]
    exact (calldataWord_bytes_at (by omega)).symm

end Benchmarks.CompoundIII.Comet
