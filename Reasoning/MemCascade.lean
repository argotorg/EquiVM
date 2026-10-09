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
def writeWord (mem : ByteArray) (off : Nat) (word : UInt256) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem off 32

/-- Chronological cascade of 32-byte word writes. -/
def writeCascade (mem : ByteArray) : List (Nat × UInt256) → ByteArray
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

theorem writeCascade_append (mem : ByteArray) (before after : List (Nat × UInt256)) :
    writeCascade mem (before ++ after) = writeCascade (writeCascade mem before) after := by
  induction before generalizing mem with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨off, word⟩
      simpa [writeCascade_cons] using ih (writeWord mem off word)

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
      toByteArray_size]
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
    (mem : ByteArray) (off : Nat) (offWord word : UInt256) (rest : List (Nat × UInt256))
    (hgap : off - mem.size < USize.size)
    (hlater : WindowDisjointFromWrites (max mem.size (off + 32)) off 32 rest)
    (hoffWord : offWord.toNat = off)
    (hmem : off < (writeCascade mem ((off, word) :: rest)).size) :
    (if offWord.toNat ≥ (writeCascade mem ((off, word) :: rest)).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((writeCascade mem ((off, word) :: rest)).readWithPadding offWord.toNat 32))) = word := by
  apply mloadWordValue_of_readWithPadding
  · omega
  · rw [hoffWord]
    exact writeCascade_read_word_of_head mem off word rest hgap hlater

end Reasoning.Theory

/-! ## Scratch regions and sparse writes -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem writeWord_sparse_eq (mem : ByteArray) (off : Nat) (word : UInt256)
    (hoff : mem.size ≤ off) :
    writeWord mem off word = mem ++ ByteArray.zeroes (off - mem.size) ++ word.toByteArray := by
  have hsz : word.toByteArray.data.size = 32 := word.toByteArrayWithSizeProof.2
  have hpz : (ByteArray.zeroes (off - mem.size)).data.size = off - mem.size :=
    ByteArray_zeroes_size _
  apply ByteArray.ext
  unfold Reasoning.Theory.writeWord ByteArray.write
  rw [if_neg (by decide : ¬ ((32 : Nat) = 0)),
    if_neg (show ¬ (0 ≥ word.toByteArray.size) from by rw [toByteArray_size]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hdsz : (mem.data ++ (ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]
    change mem.size + (off - mem.size) = off
    omega
  rw [toByteArray_size, show min 32 (32 - 0) = 32 from rfl,
    show min mem.size (off + 32) - (off + 32) = 0 by omega,
    show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) rfl]
      rfl, Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hdsz]),
    Array.extract_eq_self_of_le (show word.toByteArray.data.size ≤ 0 + (32 + 0) by rw [hsz]),
    Array.extract_eq_empty_of_le (by rw [hdsz]; omega), Array.append_empty]

theorem writeWord_sparse_size (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).size = max mem.size (off + 32) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_size mem off word (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega), ByteArray.size_append,
      ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    omega

theorem writeWord_sparse_read_preserved (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hdisj : (read + 32 ≤ off ∧ read + 32 ≤ mem.size) ∨
      (off + 32 ≤ read ∧ read + 32 ≤ mem.size)) :
    (writeWord mem off word).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_preserved mem off read word
      (by have hu := lt_usize 0 (by decide); omega) hdisj
  · have hread : read + 32 ≤ mem.size := hdisj.elim And.right And.right
    rw [writeWord_sparse_eq mem off word (by omega)]
    rw [readWithPadding_eq_extract _ read (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega), extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract _ read hread).symm

theorem writeWord_sparse_read_window (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hwithin : start + len ≤ 32) (hpos : 0 < len) (hlen : len < 2 ^ 64) :
    (writeWord mem off word).readWithPadding (off + start) len =
      word.toByteArray.extract start (start + len) := by
  by_cases hle : off ≤ mem.size
  · exact writeWord_read_window mem off start len word hwithin hpos hlen
      (by have hu := lt_usize 0 (by decide); omega)
  · rw [writeWord_sparse_eq mem off word (by omega)]
    have hprefix : (mem ++ ByteArray.zeroes (off - mem.size)).size = off := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega
    rw [readWithPadding_eq_extract' _ (off + start) len hpos hlen (by
      rw [ByteArray.size_append, hprefix, toByteArray_size]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    congr 1 <;> omega

theorem writeWord_sparse_read_back (mem : ByteArray) (off : Nat) (word : UInt256) :
    (writeWord mem off word).readWithPadding off 32 = word.toByteArray := by
  have h := writeWord_sparse_read_window mem off 0 32 word (by decide) (by decide) (by decide)
  simpa only [Nat.add_zero, Nat.zero_add,
    show word.toByteArray.extract 0 32 = word.toByteArray from by
      rw [← toByteArray_size word]
      exact byteArray_extract_self _] using h

theorem sparseCascade_read_below (mem : ByteArray) (writes : List (Nat × UInt256)) (read : Nat)
    (hin : read + 32 ≤ mem.size) (hbelow : ∀ w ∈ writes, read + 32 ≤ w.1) :
    (writeCascade mem writes).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction writes generalizing mem with
  | nil => rfl
  | cons w ws ih =>
    rw [writeCascade_cons]
    have hin' : read + 32 ≤ (writeWord mem w.1 w.2).size := by
      rw [writeWord_sparse_size]
      exact le_trans hin (Nat.le_max_left _ _)
    rw [ih (writeWord mem w.1 w.2) hin' (fun w hw ↦ hbelow w (List.mem_cons_of_mem _ hw))]
    exact writeWord_sparse_read_preserved mem w.1 read w.2
      (Or.inl ⟨hbelow w List.mem_cons_self, hin⟩)

theorem sparseCascade_read_word (mem : ByteArray) (off : Nat) (word : UInt256)
    (rest : List (Nat × UInt256)) (hlater : ∀ w ∈ rest, off + 32 ≤ w.1) :
    (writeCascade mem ((off, word) :: rest)).readWithPadding off 32 = word.toByteArray := by
  rw [writeCascade_cons, sparseCascade_read_below _ rest off
    (by rw [writeWord_sparse_size]; exact Nat.le_max_right _ _) hlater]
  exact writeWord_sparse_read_back _ _ _

/-- A low read `[read, read+32)` is unchanged by a later word write at `off ≥ read+32`. -/
theorem writeWord_read_preserved_below_of_read {mem : ByteArray} {off read : Nat} {word w : UInt256}
    (hbase : mem.readWithPadding read 32 = UInt256.toByteArray w)
    (hsz : read + 32 ≤ mem.size) (_hoff : mem.size ≤ off) (hgap : off - mem.size < USize.size)
    (hro : read + 32 ≤ off) :
    (writeWord mem off word).readWithPadding read 32 = UInt256.toByteArray w := by
  rw [writeWord_read_preserved mem off read word hgap (Or.inl ⟨hro, hsz⟩)]; exact hbase

theorem writeCascade_extract_preserved_len
    (mem : ByteArray) (writes : List (Nat × UInt256)) (read len : Nat)
    (hwin : WindowDisjointFromWrites mem.size read len writes)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hout : read + len ≤ (writeCascade mem writes).size)
    (hin : read + len ≤ mem.size) :
    (writeCascade mem writes).extract read (read + len) =
      mem.extract read (read + len) := by
  rw [← readWithPadding_eq_extract' (writeCascade mem writes) read len hpos hlen64 hout]
  rw [← readWithPadding_eq_extract' mem read len hpos hlen64 hin]
  exact writeCascade_read_preserved_len mem writes read len hwin hpos hlen64

theorem writeCascade_size_of_eq
    (base : ByteArray) (writes : List (Nat × UInt256)) (baseSize finalSize : Nat)
    (hbase : base.size = baseSize) (hgaps : WriteGapsOk base.size writes)
    (hwritesSize : writeCascadeSize baseSize writes = finalSize) :
    (writeCascade base writes).size = finalSize := by
  rw [writeCascade_size base writes hgaps, hbase]
  exact hwritesSize

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
  exact Reasoning.Theory.twoWordHashMem_size_of_ge_64' key slot hmem

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
  exact Reasoning.Theory.twoWordHashMem_read64_of_ge_96 key slot hmem hread64

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
  exact Reasoning.Theory.wordAt0Mem_read64 word hmem hread64

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
  exact Reasoning.Theory.twoWordHashMem_size_of_ge_64' key slot hmem

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
  exact Reasoning.Theory.twoWordHashMem_read0_64_of_ge key slot hmem

theorem twoWordHashMem_read0_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  exact Reasoning.Theory.twoWordHashMem_read0_of_ge64 key slot hmem

theorem twoWordHashMem_read32_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  exact Reasoning.Theory.twoWordHashMem_read32_of_ge64 key slot hmem

theorem twoWordHashMem_size_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  exact Reasoning.Theory.twoWordHashMem_size_of_ge_64' key slot hmem

theorem twoWordHashMem_read0_64_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  exact Reasoning.Theory.twoWordHashMem_read0_64_of_ge key slot hmem

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

theorem twoWordHashMem_twoWordHashMem_ge64 {mem : ByteArray}
    (key₁ slot₁ key₂ slot₂ : UInt256) (hmem : 64 ≤ mem.size) :
    64 ≤ (twoWordHashMem key₁ slot₁ (twoWordHashMem key₂ slot₂ mem)).size := by
  have hinner : 64 ≤ (twoWordHashMem key₂ slot₂ mem).size := by
    rw [twoWordHashMem_size_of_ge64 key₂ slot₂ hmem]
    exact hmem
  rw [twoWordHashMem_size_of_ge64 key₁ slot₁ hinner]
  exact hinner

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
