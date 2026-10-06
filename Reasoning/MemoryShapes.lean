import Reasoning.MemCascade

/-!
# Scratch-memory sizes and read preservation

Reusable facts for common scratch regions, independent of any contract or bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem writeWord_read64_preserved_of_ge96 {mem : ByteArray} {off : Nat} {word : UInt256}
    (hsize : 96 ≤ mem.size) (hoff : 96 ≤ off) (hgap : off - mem.size < USize.size) :
    (writeWord mem off word).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  simpa [writeWord] using
    Reasoning.Theory.writeWord_read_preserved mem off 64 word hgap
      (Or.inl ⟨by omega, by omega⟩)

theorem writeWord_read_preserved_of_disjoint {mem : ByteArray} {off read : Nat} {word : UInt256}
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (writeWord mem off word).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  simpa [writeWord] using
    Reasoning.Theory.writeWord_read_preserved mem off read word hgap hdisj

theorem writeWord_read_preserved_len_of_disjoint {mem : ByteArray} {off read len : Nat}
    {word : UInt256}
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + len ≤ off ∧ read + len ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + len ≤ mem.size))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding read len =
      mem.readWithPadding read len := by
  simpa [writeWord] using
    Reasoning.Theory.writeWord_read_preserved_len mem off read len word hgap hdisj hpos hlen64

abbrev twoWordHashMemAt
    (mem : ByteArray) (key slot : UInt256) : ByteArray :=
  writeWord (writeWord mem 0 key) 32 slot

theorem wordAt0Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt0Mem word mem).size = 160 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 160 160 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt32Mem word mem).size = 160 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 160 160 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_read0_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  exact toByteArray_extract_all slot

theorem twoWordHashMem_read0_64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem),
      twoWordHashMem_read0_160 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem),
      twoWordHashMem_read32_160 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_size_164 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 164) :
    (wordAt0Mem word mem).size = 164 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_164 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 164) :
    (wordAt32Mem word mem).size = 164 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_164 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 164) :
    (twoWordHashMem key slot mem).size = 164 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_164 slot (wordAt0Mem_size_164 key hmem)

/-- The store's output buffer keeps the free pointer at `[64,96)` (writes at `[0,64)` and `[128,164)`
    don't touch it). -/
theorem twoWordHashMem_read64_preserve (key slot : UInt256) {mem : ByteArray} (h : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  have hinner : ((UInt256.toByteArray key).write 0 mem 0 32).size = mem.size := by
    rw [write32_eq (UInt256.toByteArray key) mem 0 (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by rw [hinner]; omega) (by omega)
      (by rw [hinner]; omega),
    write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega),
      hread64]

theorem wordAt0Mem_size_320 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 320) : (wordAt0Mem word mem).size = 320 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 320 320 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_320 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 320) : (wordAt32Mem word mem).size = 320 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 320 320 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_read0_64_320 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 320) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
    unfold twoWordHashMem
    rw [wordAt32Mem_size_320]
    · omega
    · exact wordAt0Mem_size_320 key hmem)]
  have hleft : (twoWordHashMem key slot mem).extract 0 32 =
      UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
      unfold twoWordHashMem
      rw [wordAt32Mem_size_320]
      · omega
      · exact wordAt0Mem_size_320 key hmem)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_320 key hmem]; omega) (by omega)]
    exact wordAt0Mem_read0 key mem
  have hright : (twoWordHashMem key slot mem).extract 32 64 =
      UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
      unfold twoWordHashMem
      rw [wordAt32Mem_size_320]
      · omega
      · exact wordAt0Mem_size_320 key hmem)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_320 key hmem]; omega)]
    exact toByteArray_extract_all slot
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
      (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_read_preserved_320 {mem : ByteArray}
    (key slot : UInt256) (read : Nat) (hmem : mem.size = 320) (hread : 64 ≤ read)
    (hwindow : read + 32 ≤ 320) :
    (twoWordHashMem key slot mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above (UInt256.toByteArray slot) (wordAt0Mem key mem) 32 read
    (by rw [toByteArray_size]) (by rw [wordAt0Mem_size_320 key hmem]; omega)
    (by omega) (by rw [wordAt0Mem_size_320 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above (UInt256.toByteArray key) mem 0 read
    (by rw [toByteArray_size]) (by rw [hmem]; omega) (by omega) (by rw [hmem]; omega)]

theorem twoWordHashMem_size_ge_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    64 ≤ (twoWordHashMem key slot mem).size := by
  have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
    simpa [wordAt0Mem] using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  simpa [twoWordHashMem, wordAt32Mem] using
    toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32
      (lt_usize (32 - (wordAt0Mem key mem).size) (by omega))

theorem twoWordHashMem_size_of_ge_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeCascade mem [(0, key), (32, slot)]).size = mem.size
  exact writeCascade_size_of_base mem [(0, key), (32, slot)] rfl
    (by simp [WriteGapsOk])
    (by
      simp [writeCascadeSize]
      omega)

theorem twoWordHashMem_read0_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)
      (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read32_of_ge {mem : ByteArray} (key slot : UInt256)
    (_hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size])
      (by
        have hword0 : 32 ≤ (wordAt0Mem key mem).size := by
          simpa [wordAt0Mem] using
            toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
        omega)]
  rw [toByteArray_extract_all]

set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split _ 0 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (twoWordHashMem_size_ge_64_of_ge key slot hmem)]
  rw [twoWordHashMem_read0_of_ge key slot hmem, twoWordHashMem_read32_of_ge key slot hmem]

theorem twoWordHashMem_read64_of_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeCascade mem [(0, key), (32, slot)]).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [writeCascade_read_preserved_of_base mem [(0, key), (32, slot)] rfl]
  · exact hread64
  · simp [WindowDisjointFromWrites]
    omega

theorem wordAt32TwoWordHashMem_read0_64 {mem : ByteArray}
    (key oldSlot newSlot : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray newSlot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
        omega)]
  have hleft :
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 32 =
        UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by
          rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
          omega)]
    unfold wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega) (by omega)]
    exact twoWordHashMem_read0 key oldSlot hmem
  have hright :
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 32 64 =
        UInt256.toByteArray newSlot := by
    rw [← readWithPadding_eq_extract _ 32
        (by
          rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
          omega)]
    unfold wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray newSlot).size ≤ 32
      rw [toByteArray_size])
  rw [show (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 64 =
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 32 ++
        (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem wordAt32TwoWordHashMem_read64 {mem : ByteArray}
    (key oldSlot newSlot : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega) (by omega)
    (by rw [twoWordHashMem_size_96 key oldSlot hmem])]
  exact twoWordHashMem_read64 key oldSlot hmem hread64

theorem wordAt0Mem_read64_of_size96 {mem : ByteArray}
    (word : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega) (by rw [hmem])]
  exact hread64

theorem twoWordHashMem_size_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).size = 160 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_160 slot (wordAt0Mem_size_160 key hmem)

theorem twoWordHashMem_read64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_160 key hmem]; norm_num)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; norm_num)]
  exact hread64

theorem twoWordHashMem_read64_160_ptr160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMemAt_size {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMemAt mem key slot).size = mem.size := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkey : (writeWord mem 0 key).size = mem.size := by
    rw [writeWord_size]
    · omega
    · omega
  unfold twoWordHashMemAt
  rw [writeWord_size]
  · rw [hkey]
    omega
  · rw [hkey]
    omega

theorem twoWordHashMemAt_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMemAt mem key slot).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkeySize : (writeWord mem 0 key).size = mem.size := by
    rw [writeWord_size]
    · omega
    · omega
  calc
    (twoWordHashMemAt mem key slot).readWithPadding 64 32 =
        (writeWord mem 0 key).readWithPadding 64 32 := by
      simpa [twoWordHashMemAt] using
        writeWord_read_preserved_of_disjoint
          (mem := writeWord mem 0 key) (off := 32) (read := 64) (word := slot)
          (hgap := by rw [hkeySize]; omega)
          (hdisj := Or.inr ⟨by norm_num, by rw [hkeySize]; omega⟩)
    _ = mem.readWithPadding 64 32 := by
      simpa using
        writeWord_read_preserved_of_disjoint
          (mem := mem) (off := 0) (read := 64) (word := key)
          (hgap := by omega)
          (hdisj := Or.inr ⟨by norm_num, by omega⟩)

set_option maxHeartbeats 800000 in
theorem twoWordHashMemAt_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMemAt mem key slot).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hzero : 0 < USize.size := lt_usize 0 (by norm_num)
  have hkeySize : (writeWord mem 0 key).size = mem.size := by
    rw [writeWord_size]
    · omega
    · omega
  have hhashSize : (twoWordHashMemAt mem key slot).size = mem.size :=
    twoWordHashMemAt_size key slot hmem
  have hread0 :
      (twoWordHashMemAt mem key slot).readWithPadding 0 32 =
        UInt256.toByteArray key := by
    calc
      (twoWordHashMemAt mem key slot).readWithPadding 0 32 =
          (writeWord mem 0 key).readWithPadding 0 32 := by
        simpa [twoWordHashMemAt] using
          writeWord_read_preserved_of_disjoint
            (mem := writeWord mem 0 key) (off := 32) (read := 0) (word := slot)
            (hgap := by rw [hkeySize]; omega)
            (hdisj := Or.inl ⟨by norm_num, by rw [hkeySize]; omega⟩)
      _ = UInt256.toByteArray key := by
        simpa using writeWord_read_back mem 0 key (by omega)
  have hread32 :
      (twoWordHashMemAt mem key slot).readWithPadding 32 32 =
        UInt256.toByteArray slot := by
    simpa [twoWordHashMemAt] using
      writeWord_read_back (writeWord mem 0 key) 32 slot
        (by rw [hkeySize]; omega)
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hhashSize]; omega)]
  have hleft :
      (twoWordHashMemAt mem key slot).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hhashSize]; omega), hread0]
  have hright :
      (twoWordHashMemAt mem key slot).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hhashSize]; omega), hread32]
  rw [show (twoWordHashMemAt mem key slot).extract 0 64 =
      (twoWordHashMemAt mem key slot).extract 0 32 ++
        (twoWordHashMemAt mem key slot).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_read64_of_size_96 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (wordAt0Mem word mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega) (by rw [hmem])]

theorem wordAt0Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt0Mem word mem).size = 192 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt32Mem word mem).size = 192 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_read0_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega)]
  exact toByteArray_extract_all slot

theorem twoWordHashMem_read0_64_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem),
      twoWordHashMem_read0_192 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem),
      twoWordHashMem_read32_192 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_size_256 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 256) :
    (wordAt0Mem word mem).size = 256 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_256 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 256) :
    (wordAt32Mem word mem).size = 256 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).size = 256 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_256 slot (wordAt0Mem_size_256 key hmem)

theorem twoWordHashMem_read0_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_256 {mem : ByteArray} (key slot ptr : UInt256)
    (hmem : mem.size = 256)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ptr) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ptr := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_256 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read0_64_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_256 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_256 key slot hmem]; omega),
      twoWordHashMem_read0_256 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_256 key slot hmem]; omega),
      twoWordHashMem_read32_256 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      simp]
  rw [hleft, hright]

theorem wordAt0Mem_size_580 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 580) :
    (wordAt0Mem word mem).size = 580 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_580 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 580) :
    (wordAt32Mem word mem).size = 580 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem twoWordHashMem_size_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).size = 580 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_580 slot (wordAt0Mem_size_580 key hmem)

theorem twoWordHashMem_read0_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read0_64_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_580 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_580 key slot hmem]; omega),
      twoWordHashMem_read0_580 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_580 key slot hmem]; omega),
      twoWordHashMem_read32_580 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      simp]
  rw [hleft, hright]

theorem twoWordHashMem_read64_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read256_580 {mem : ByteArray} (key slot word : UInt256)
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (twoWordHashMem key slot mem).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 256 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 256 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread256

theorem twoWordHashMem_mload256_580 {mem : ByteArray} (key slot word : UInt256)
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (if (⟨256⟩ : UInt256).toNat ≥ (twoWordHashMem key slot mem).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((twoWordHashMem key slot mem).readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      word := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (v := word)
    (by rw [twoWordHashMem_size_580 key slot hmem]; decide)
    (by
      simpa [show (⟨256⟩ : UInt256).toNat = 256 by decide] using
        twoWordHashMem_read256_580 key slot word hmem hread256)

theorem wordAt0Mem_size_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (wordAt0Mem word mem).size = 260 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 260 260 hmem (by omega) (by omega)

theorem wordAt32Mem_size_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (wordAt32Mem word mem).size = 260 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 260 260 hmem (by omega) (by omega)

theorem wordAt32Mem_read64_260 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
    (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem wordAt32Mem_read0_64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread0 : mem.readWithPadding 0 32 = UInt256.toByteArray key) :
    (wordAt32Mem slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsize : (wordAt32Mem slot mem).size = 260 :=
    wordAt32Mem_size_260 slot hmem
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (wordAt32Mem slot mem) 0 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize]; omega)]
  have hleft :
      (wordAt32Mem slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
    unfold wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega)]
    exact hread0
  have hright :
      (wordAt32Mem slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt32Mem
    rw [write32_read_back _ _ 32 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
    rw [toByteArray_extract_all]
  rw [hleft, hright]

theorem twoWordHashMem_size_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).size = 260 := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32 260 260
    (wordAt0Mem_size_260 key hmem)
    (by rw [wordAt0Mem_size_260 key hmem]; omega) (by omega)

theorem twoWordHashMem_read64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_260 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_260 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read0_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_260 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_260 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read0_64_260 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 260) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_260 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_260 key slot hmem]; omega),
      twoWordHashMem_read0_260 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_260 key slot hmem]; omega),
      twoWordHashMem_read32_260 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge64 key hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    wordAt0Mem_size_of_ge64 key hmem]
  omega

theorem twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge64 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ 0 (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ 32 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge64 key hmem]; omega)]
  rw [toByteArray_extract_all]

theorem twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_size_228 (word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (wordAt0Mem word mem).size = 228 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 228 228 hmem (by omega) (by omega)

theorem twoWordHashMem_size_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).size = 228 := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le (wordAt0Mem key mem) slot 32 228 228
    (wordAt0Mem_size_228 key hmem)
    (by rw [wordAt0Mem_size_228 key hmem]; omega) (by omega)

theorem twoWordHashMem_read64_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_228 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_228 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read0_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_228 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_228 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read0_64_228 (key slot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_228 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_228 key slot hmem]; omega),
      twoWordHashMem_read0_228 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_228 key slot hmem]; omega),
      twoWordHashMem_read32_228 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_read0_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by decide)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [hword0Size]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by decide)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [hword0Size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_size_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by decide)
  unfold twoWordHashMem wordAt32Mem
  change (writeWord (wordAt0Mem key mem) 32 slot).size = mem.size
  rw [writeWord_size]
  · rw [hword0Size]
    omega
  · rw [hword0Size]
    have hzero : 32 - mem.size = 0 := by omega
    rw [hzero]
    exact lt_usize 0 (by decide)

theorem twoWordHashMem_read0_64_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsize := twoWordHashMem_size_of_size_ge (mem := mem) key slot hmem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsize]; omega),
      twoWordHashMem_read0_of_size_ge key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsize]; omega),
      twoWordHashMem_read32_of_size_ge key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_size_ge_64 (key slot : UInt256) (mem : ByteArray) :
    64 ≤ (twoWordHashMem key slot mem).size := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  simpa using
    toByteArray_write_size_ge_off_add32 slot (wordAt0Mem key mem) 32 (by
      have hzero : 32 - (wordAt0Mem key mem).size = 0 := by omega
      rw [hzero]
      exact lt_usize 0 (by norm_num))

theorem twoWordHashMem_read0_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) hkeySize (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hkeySize : 32 ≤ (wordAt0Mem key mem).size := by
    unfold wordAt0Mem
    simpa using
      toByteArray_write_size_ge_off_add32 key mem 0 (by simp)
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back (wordAt0Mem key mem) slot 32 hkeySize

theorem twoWordHashMem_read0_64_any (key slot : UInt256) (mem : ByteArray) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [byteArray_readWithPadding_split (twoWordHashMem key slot mem) 0 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa using twoWordHashMem_size_ge_64 key slot mem)]
  rw [twoWordHashMem_read0_any, twoWordHashMem_read32_any]

theorem wordAt0Mem_size_224 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 224) :
    (wordAt0Mem word mem).size = 224 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 224 224 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_224 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 224) :
    (wordAt32Mem word mem).size = 224 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 224 224 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_read0_224 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 224) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below_len _ _ 32 0 32 (by rw [toByteArray_size])
    (by rw [wordAt0Mem_size_224 key hmem]; omega) (by omega)
    (by rw [wordAt0Mem_size_224 key hmem]; omega) (by decide) (by norm_num)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_224 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 224) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write_read_back_of_gap slot (wordAt0Mem key mem) 32
    (by rw [wordAt0Mem_size_224 key hmem]; exact lt_usize 0 (by decide))

theorem twoWordHashMem_read0_64_224 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 224) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_224]
        · omega
        · exact wordAt0Mem_size_224 key hmem)]
  have h0 :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract' (twoWordHashMem key slot mem) 0 32
        (by norm_num) (by norm_num) (by
          unfold twoWordHashMem
          rw [wordAt32Mem_size_224]
          · omega
          · exact wordAt0Mem_size_224 key hmem),
      twoWordHashMem_read0_224 key slot hmem]
  have h32 :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract' (twoWordHashMem key slot mem) 32 32
        (by norm_num) (by norm_num) (by
          unfold twoWordHashMem
          rw [wordAt32Mem_size_224]
          · omega
          · exact wordAt0Mem_size_224 key hmem),
      twoWordHashMem_read32_224 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num, h0, h32]

theorem wordAt0Mem_read64_preserved_key (key : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (wordAt0Mem key mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by rw [hmem])]

theorem twoWordHashMem_read64_preserved_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge_32 key (by omega)]; omega) (by omega)
      (by rw [wordAt0Mem_size_of_ge_32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]

theorem twoWordHashMem_read64_of_size576 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 576)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨576⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨576⟩ := by
  rw [twoWordHashMem_read64_preserved_of_ge96]
  · exact hread64
  · rw [hmem]
    omega

theorem twoWordHashMem_read32_above64 {mem : ByteArray} (key slot : UInt256)
    {readOff : Nat} (habove : 64 ≤ readOff) (hin : readOff + 32 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  have hmem32 : 32 ≤ mem.size := by omega
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 readOff (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge_32 key hmem32]; omega)
      (by omega)
      (by rw [wordAt0Mem_size_of_ge_32 key hmem32]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 readOff (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]

theorem twoWordHashMem_size_576 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 576) :
    (twoWordHashMem key slot mem).size = 576 := by
  rw [twoWordHashMem_size_of_ge64]
  · exact hmem
  · rw [hmem]
    omega

theorem twoWordHashMem_twoWordHashMem_ge64 {mem : ByteArray}
    (key₁ slot₁ key₂ slot₂ : UInt256) (hmem : 64 ≤ mem.size) :
    64 ≤ (twoWordHashMem key₁ slot₁ (twoWordHashMem key₂ slot₂ mem)).size := by
  have hinner : 64 ≤ (twoWordHashMem key₂ slot₂ mem).size := by
    rw [twoWordHashMem_size_of_ge64 key₂ slot₂ hmem]
    exact hmem
  rw [twoWordHashMem_size_of_ge64 key₁ slot₁ hinner]
  exact hinner

theorem twoWordHashMem_read32_above64_of_size576 {mem : ByteArray}
    (key slot : UInt256) {readOff : Nat} {word : UInt256}
    (habove : 64 ≤ readOff) (hin : readOff + 32 ≤ 576) (hmem : mem.size = 576)
    (hread : mem.readWithPadding readOff 32 = UInt256.toByteArray word) :
    (twoWordHashMem key slot mem).readWithPadding readOff 32 =
      UInt256.toByteArray word := by
  rw [twoWordHashMem_read32_above64 key slot habove]
  · exact hread
  · rw [hmem]
    exact hin

/-- `wordAt0Mem` leaves the free-pointer slot (bytes 64–95) untouched (local copy of the private
    `TransferFrom.wtf_wordAt0Mem_read64`). -/
theorem wordAt0Mem_read64_preserved_word (word : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    (wordAt0Mem word mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega) (by omega)
    (by rw [hmem])]

/-- `wordAt0Mem` leaves the free-pointer slot (bytes 64–95) untouched. -/
theorem wordAt0Mem_read64_preserved_of_size96 {m : ByteArray} (word : UInt256) (hm : m.size = 96) :
    (wordAt0Mem word m).readWithPadding 64 32 = m.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hm]; omega) (by omega)
    (by rw [hm])]







def writeWordMem (off : Nat) (word : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray word).write 0 mem off 32

theorem writeWordMem_size_of_contains {mem : ByteArray} {off : Nat} {word : UInt256}
    (hcontains : off + 32 ≤ mem.size) :
    (writeWordMem off word mem).size = mem.size := by
  unfold writeWordMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem writeWordMem_size_at_end {mem : ByteArray} {off : Nat} {word : UInt256}
    (hend : mem.size = off) :
    (writeWordMem off word mem).size = off + 32 := by
  unfold writeWordMem
  have hgap : off - mem.size < USize.size := by
    rw [hend, Nat.sub_self]
    exact USize.size_pos
  rw [toByteArray_write_eq _ _ _ (by omega) hgap,
    ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
    toByteArray_size]
  omega

theorem writeWordMem_read64_below {mem : ByteArray} {off : Nat} {word : UInt256}
    (hcontains : 64 + 32 ≤ mem.size) (hsep : 64 + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    (writeWordMem off word mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  unfold writeWordMem
  exact toByteArray_write_read_below_of_gap word mem off 64 hcontains hsep hgap

theorem writeWordMem_read32_below {mem : ByteArray} {off readOff : Nat} {word : UInt256}
    (hcontains : readOff + 32 ≤ mem.size) (hsep : readOff + 32 ≤ off)
    (hgap : off - mem.size < USize.size) :
    (writeWordMem off word mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  unfold writeWordMem
  exact toByteArray_write_read_below_of_gap word mem off readOff hcontains hsep hgap

theorem writeWordMem_read32_above {mem : ByteArray} {off readOff : Nat} {word : UInt256}
    (hlo : off ≤ mem.size) (habove : off + 32 ≤ readOff)
    (hin : readOff + 32 ≤ mem.size) :
    (writeWordMem off word mem).readWithPadding readOff 32 =
      mem.readWithPadding readOff 32 := by
  unfold writeWordMem
  exact write32_read_above _ _ off readOff (by rw [toByteArray_size]) hlo habove hin

theorem threeScratchWrites_preserve_fp {mem : ByteArray}
    {fp key slot data : UInt256}
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) :
    let mem1 := (UInt256.toByteArray key).write 0 mem 0 32
    let mem2 := (UInt256.toByteArray slot).write 0 mem1 32 32
    let mem3 := (UInt256.toByteArray data).write 0 mem2 0 32
    mem3.readWithPadding 64 32 = UInt256.toByteArray fp ∧ mem3.size = mem.size := by
  intro mem1 mem2 mem3
  have hmem1_read : mem1.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem1]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega)]
    exact hread
  have hmem1_size : mem1.size = mem.size := by
    dsimp [mem1]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have hmem2_read : mem2.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem2]
    rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])]
    · exact hmem1_read
    · rw [hmem1_size]
      omega
    · omega
    · rw [hmem1_size]
      omega
  have hmem2_size : mem2.size = mem.size := by
    dsimp [mem2]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem1_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem1_size]
    omega
  have hmem3_read : mem3.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem3]
    rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])]
    · exact hmem2_read
    · rw [hmem2_size]
      omega
    · omega
    · rw [hmem2_size]
      omega
  have hmem3_size : mem3.size = mem.size := by
    dsimp [mem3]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem2_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size]
    omega
  exact ⟨hmem3_read, hmem3_size⟩

end Reasoning.Theory
