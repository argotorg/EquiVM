import Reasoning.Memory

/-!
# Memory write cascades

This module packages the repeated EVM-memory proof pattern where a trace builds a concrete memory
buffer by a chronological list of 32-byte word writes.  The single-write byte facts live in
`Reasoning.Memory`; this file composes them over a write list.
-/

open Ethereum Ethereum.EVM Solm ABI

namespace Reasoning.Theory

/-- A single EVM-style 32-byte word write. -/
noncomputable def writeWord (mem : ByteArray) (off : Nat) (word : UInt256) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem off 32

/-- Chronological cascade of 32-byte word writes. -/
noncomputable def writeCascade (mem : ByteArray) : List (Nat × UInt256) → ByteArray
  | [] => mem
  | (off, word) :: rest => writeCascade (writeWord mem off word) rest

/-- The expected memory size after the same chronological cascade, ignoring byte contents. -/
def writeCascadeSize : Nat → List (Nat × UInt256) → Nat
  | size, [] => size
  | size, (off, _) :: rest => writeCascadeSize (max size (off + 32)) rest

/-- No word write in the cascade wraps the platform `USize` gap. -/
def WriteGapsOk : Nat → List (Nat × UInt256) → Prop
  | _, [] => True
  | size, (off, _) :: rest =>
      off - size < USize.size ∧ WriteGapsOk (max size (off + 32)) rest

/-- A read window is disjoint from every write in the cascade and already lies inside the memory
    available at each step. -/
def WindowDisjointFromWrites : Nat → Nat → Nat → List (Nat × UInt256) → Prop
  | _, _, _, [] => True
  | size, read, len, (off, _) :: rest =>
      off - size < USize.size ∧
        (((read + len ≤ off ∧ read + len ≤ size) ∨
          (off + 32 ≤ read ∧ read + len ≤ size)) ∧
        WindowDisjointFromWrites (max size (off + 32)) read len rest)

@[simp] theorem writeCascade_nil (mem : ByteArray) :
    writeCascade mem [] = mem := rfl

@[simp] theorem writeCascade_cons (mem : ByteArray) (off : Nat) (word : UInt256)
    (rest : List (Nat × UInt256)) :
    writeCascade mem ((off, word) :: rest) = writeCascade (writeWord mem off word) rest := rfl

@[simp] theorem writeCascadeSize_nil (size : Nat) :
    writeCascadeSize size [] = size := rfl

@[simp] theorem writeCascadeSize_cons (size off : Nat) (word : UInt256)
    (rest : List (Nat × UInt256)) :
    writeCascadeSize size ((off, word) :: rest) =
      writeCascadeSize (max size (off + 32)) rest := rfl

theorem writeWord_size (mem : ByteArray) (off : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) :
    (writeWord mem off word).size = max mem.size (off + 32) := by
  unfold writeWord
  by_cases hle : off ≤ mem.size
  · rw [write32_eq _ _ off (by rw [toByteArray_size]) hle]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write_eq _ _ off hge hgap]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
      USize.toNat_ofNat_of_lt' hgap, toByteArray_size]
    omega

theorem writeCascade_size (mem : ByteArray) (writes : List (Nat × UInt256))
    (hok : WriteGapsOk mem.size writes) :
    (writeCascade mem writes).size = writeCascadeSize mem.size writes := by
  induction writes generalizing mem with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨off, word⟩
      rcases hok with ⟨hgap, hrest⟩
      rw [writeCascade_cons, writeCascadeSize_cons]
      have hsize : (writeWord mem off word).size = max mem.size (off + 32) :=
        writeWord_size mem off word hgap
      calc
        (writeCascade (writeWord mem off word) rest).size =
            writeCascadeSize (writeWord mem off word).size rest :=
          ih (writeWord mem off word) (by simpa [hsize] using hrest)
        _ = writeCascadeSize (max mem.size (off + 32)) rest := by rw [hsize]

theorem writeCascade_size_of_base
    (mem : ByteArray) (writes : List (Nat × UInt256)) {base out : Nat}
    (hbase : mem.size = base)
    (hok : WriteGapsOk base writes)
    (hsize : writeCascadeSize base writes = out) :
    (writeCascade mem writes).size = out := by
  have hok' : WriteGapsOk mem.size writes := by simpa [hbase] using hok
  rw [writeCascade_size mem writes hok', hbase, hsize]

theorem writeWord_read_preserved_len
    (mem : ByteArray) (off read len : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + len ≤ off ∧ read + len ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + len ≤ mem.size))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  unfold writeWord
  rcases hdisj with hbelow | habove
  · exact toByteArray_write_read_below_len_of_gap word mem off read len
      hbelow.2 hbelow.1 hpos hlen64 hgap
  · have hle : off ≤ mem.size := by omega
    exact write32_read_above_len _ _ off read len (by rw [toByteArray_size]) hle
      habove.1 habove.2 hpos hlen64

theorem writeWord_read_preserved
    (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size)
    (hdisj :
      (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (writeWord mem off word).readWithPadding read 32 = mem.readWithPadding read 32 :=
  writeWord_read_preserved_len mem off read 32 word hgap hdisj (by norm_num) (by norm_num)

theorem writeWord_read_window
    (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    (writeWord mem off word).readWithPadding (off + start) len =
      (UInt256.toByteArray word).extract start (start + len) := by
  unfold writeWord
  exact toByteArray_write_read_window_of_gap word mem off start len hwithin hpos hlen64 hgap

theorem writeWord_read_back (mem : ByteArray) (off : Nat) (word : UInt256)
    (hgap : off - mem.size < USize.size) :
    (writeWord mem off word).readWithPadding off 32 = UInt256.toByteArray word := by
  change (writeWord mem off word).readWithPadding (off + 0) 32 = UInt256.toByteArray word
  rw [writeWord_read_window mem off 0 32 word (by norm_num) (by norm_num) (by norm_num) hgap]
  exact toByteArray_extract_all word

theorem writeCascade_read_preserved_len
    (mem : ByteArray) (writes : List (Nat × UInt256)) (read len : Nat)
    (hwin : WindowDisjointFromWrites mem.size read len writes)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (writeCascade mem writes).readWithPadding read len = mem.readWithPadding read len := by
  induction writes generalizing mem with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨off, word⟩
      rcases hwin with ⟨hgap, hdisj, hrest⟩
      rw [writeCascade_cons]
      have hsize : (writeWord mem off word).size = max mem.size (off + 32) :=
        writeWord_size mem off word hgap
      rw [ih (writeWord mem off word) (by simpa [hsize] using hrest)]
      exact writeWord_read_preserved_len mem off read len word hgap hdisj hpos hlen64

theorem writeCascade_read_preserved
    (mem : ByteArray) (writes : List (Nat × UInt256)) (read : Nat)
    (hwin : WindowDisjointFromWrites mem.size read 32 writes) :
    (writeCascade mem writes).readWithPadding read 32 = mem.readWithPadding read 32 :=
  writeCascade_read_preserved_len mem writes read 32 hwin (by norm_num) (by norm_num)

theorem writeCascade_read_preserved_of_base
    (mem : ByteArray) (writes : List (Nat × UInt256)) {base read : Nat}
    (hbase : mem.size = base)
    (hwin : WindowDisjointFromWrites base read 32 writes) :
    (writeCascade mem writes).readWithPadding read 32 = mem.readWithPadding read 32 := by
  exact writeCascade_read_preserved mem writes read (by simpa [hbase] using hwin)

theorem writeCascade_read_window_of_head
    (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (rest : List (Nat × UInt256))
    (hgap : off - mem.size < USize.size)
    (hlater :
      WindowDisjointFromWrites (max mem.size (off + 32)) (off + start) len rest)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding (off + start) len =
      (UInt256.toByteArray word).extract start (start + len) := by
  rw [writeCascade_cons]
  have hsize : (writeWord mem off word).size = max mem.size (off + 32) :=
    writeWord_size mem off word hgap
  rw [writeCascade_read_preserved_len (writeWord mem off word) rest (off + start) len
    (by simpa [hsize] using hlater) hpos hlen64]
  exact writeWord_read_window mem off start len word hwithin hpos hlen64 hgap

theorem writeCascade_read_word_of_head
    (mem : ByteArray) (off : Nat) (word : UInt256) (rest : List (Nat × UInt256))
    (hgap : off - mem.size < USize.size)
    (hlater : WindowDisjointFromWrites (max mem.size (off + 32)) off 32 rest) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding off 32 =
      UInt256.toByteArray word := by
  change (writeCascade mem ((off, word) :: rest)).readWithPadding (off + 0) 32 =
    UInt256.toByteArray word
  rw [writeCascade_read_window_of_head mem off 0 32 word rest hgap hlater
    (by norm_num) (by norm_num) (by norm_num)]
  exact toByteArray_extract_all word

theorem writeCascade_read_word_of_head_of_base
    (mem : ByteArray) {base off : Nat} (word : UInt256) (rest : List (Nat × UInt256))
    (hbase : mem.size = base)
    (hgap : off - base < USize.size)
    (hlater : WindowDisjointFromWrites (max base (off + 32)) off 32 rest) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding off 32 =
      UInt256.toByteArray word := by
  exact writeCascade_read_word_of_head mem off word rest
    (by simpa [hbase] using hgap)
    (by simpa [hbase] using hlater)

theorem writeCascade_mload_word_of_head
    (mem : ByteArray) (off : Nat) (offWord aw word : UInt256) (rest : List (Nat × UInt256))
    (hgap : off - mem.size < USize.size)
    (hlater : WindowDisjointFromWrites (max mem.size (off + 32)) off 32 rest)
    (hoffWord : offWord.toNat = off)
    (hmem : off < (writeCascade mem ((off, word) :: rest)).size)
    (haw : ¬ offWord ≥ aw * ⟨32⟩) :
    (if offWord.toNat ≥ (writeCascade mem ((off, word) :: rest)).size ∨
        offWord ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((writeCascade mem ((off, word) :: rest)).readWithPadding offWord.toNat 32))) = word := by
  apply mloadWordValue_of_readWithPadding
  · omega
  · exact haw
  · rw [hoffWord]
    exact writeCascade_read_word_of_head mem off word rest hgap hlater

end Reasoning.Theory
