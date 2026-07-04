import Examples.TinyImmutable.Bytecode
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.Solc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

set_option maxRecDepth 10000

@[simp] theorem wordBytesBEArray_size (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray).size = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

@[simp] theorem wordBytesBEArray_eq_toByteArray (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray) = UInt256.toByteArray w := by
  apply ByteArray.ext
  have h := congrArg ByteArray.data (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa using h

@[simp] theorem tinyImmutableBytecode_size : tinyImmutableBytecode.size = 432 := by
  native_decide +revert

@[simp] theorem tinyImmutableCreationBytecode_size :
    tinyImmutableCreationBytecode.size = 634 := by
  native_decide +revert

def runtimeWrites (v : TinyImmutables) : List (Nat × UInt256) :=
  [ (186, EVM.wordOfInt (Int.ofNat v.scale.toNat)),
    (361, EVM.wordOfInt (Int.ofNat v.scale.toNat)),
    (72, EVM.Word.ofNat (↑v.owner : Nat)),
    (245, EVM.Word.ofNat (↑v.owner : Nat)) ]

noncomputable def patchedRuntime (v : TinyImmutables) : ByteArray :=
  writeCascade tinyImmutableBytecode (runtimeWrites v)

abbrev ownerSelBytes : ByteArray := ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
abbrev quoteSelBytes : ByteArray := ⟨#[0xed, 0x1b, 0xd7, 0x6c]⟩
abbrev scaleSelBytes : ByteArray := ⟨#[0xf5, 0x1e, 0x18, 0x1a]⟩

abbrev tinyFirstArmPc : UInt256 := ⟨30⟩

/-- Selector fact: `keccak256("owner()")[0:4]`. -/
axiom ownerSelectorOf (v : TinyImmutables) :
    selectorOf (ownerTransition v) = ownerSelBytes

/-- Selector fact: `keccak256("quote(uint256)")[0:4]`. -/
axiom quoteSelectorOf (v : TinyImmutables) :
    selectorOf (quoteTransition v) = quoteSelBytes

/-- Selector fact: `keccak256("scale()")[0:4]`. -/
axiom scaleSelectorOf (v : TinyImmutables) :
    selectorOf (scaleTransition v) = scaleSelBytes

theorem ownerSelBytes_size : ownerSelBytes.size = 4 := rfl
theorem quoteSelBytes_size : quoteSelBytes.size = 4 := rfl
theorem scaleSelBytes_size : scaleSelBytes.size = 4 := rfl

theorem accountAddress_ofNat_toNat (a : AccountAddress) :
    AccountAddress.ofNat a.toNat = a := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt a.isLt

theorem accountAddress_ofNat_val (a : AccountAddress) :
    AccountAddress.ofNat (↑a : Nat) = a :=
  accountAddress_ofNat_toNat a

theorem evalAddrLit (cfg : Config) (frame : Frame) (evm : EVM.State) (a : AccountAddress) :
    evalExpr? cfg frame evm (addrLit a) = .ok (.address a) := by
  simp only [addrLit, evalExpr?, EvalResult.bind, bind, pure, castValue?]
  rw [if_neg]
  · simp [EvalResult.ofOption, accountAddress_ofNat_val]
  · exact not_lt.mpr (Int.natCast_nonneg (↑a : Nat))

theorem spliceBytes_toByteArray_eq_writeWord (mem : ByteArray) (off : Nat) (w : UInt256)
    (h : off + 32 ≤ mem.size) :
    spliceBytes? mem off (UInt256.toByteArray w) = some (writeWord mem off w) := by
  unfold spliceBytes? Reasoning.Theory.writeWord
  rw [toByteArray_size, if_pos h]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem patchRuntime_eq_patchedRuntime (v : TinyImmutables) :
    patchRuntime tinyImmutableBytecode (patches v) = some (patchedRuntime v) := by
  simp [patchedRuntime, patchRuntime, patches, patchesFrom, offsets, immValues, wordBytes?,
    valueToWord, List.lookup_cons, runtimeWrites, writeCascade]
  rw [spliceBytes_toByteArray_eq_writeWord tinyImmutableBytecode 186]
  · simp
    have hgap186 : 186 - tinyImmutableBytecode.size < USize.size := by
      rw [tinyImmutableBytecode_size]
      norm_num
    have hsize186 :
        (writeWord tinyImmutableBytecode 186
          (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size = 432 := by
      rw [writeWord_size _ _ _ hgap186]
      rw [tinyImmutableBytecode_size]
      norm_num
    have h361 := spliceBytes_toByteArray_eq_writeWord
      (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
      (EVM.wordOfInt (Int.ofNat v.scale.toNat))
      (by rw [hsize186]; norm_num)
    cases hsp361 : spliceBytes?
        (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
        (UInt256.toByteArray (EVM.wordOfInt (Int.ofNat v.scale.toNat))) with
    | none =>
        rw [hsp361] at h361
        cases h361
    | some p361 =>
        rw [hsp361] at h361
        cases h361
        dsimp [Option.bind]
        have hgap361 :
            361 - (writeWord tinyImmutableBytecode 186
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size < USize.size := by
          rw [hsize186]
          norm_num
        have hsize361 :
            (writeWord
              (writeWord tinyImmutableBytecode 186
                (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size = 432 := by
          rw [writeWord_size _ _ _ hgap361]
          rw [hsize186]
          norm_num
        have h72 := spliceBytes_toByteArray_eq_writeWord
          (writeWord
            (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
            (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
          (EVM.Word.ofNat (↑v.owner : Nat))
          (by rw [hsize361]; norm_num)
        cases hsp72 : spliceBytes?
            (writeWord
              (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
              (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
            (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) with
        | none =>
            rw [hsp72] at h72
            cases h72
        | some p72 =>
            rw [hsp72] at h72
            cases h72
            dsimp [Option.bind]
            have hgap72 :
                72 - (writeWord
                  (writeWord tinyImmutableBytecode 186
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                  (EVM.wordOfInt (Int.ofNat v.scale.toNat))).size < USize.size := by
              rw [hsize361]
              norm_num
            have hsize72 :
                (writeWord
                  (writeWord
                    (writeWord tinyImmutableBytecode 186
                      (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                  (EVM.Word.ofNat (↑v.owner : Nat))).size = 432 := by
              rw [writeWord_size _ _ _ hgap72]
              rw [hsize361]
              norm_num
            have h245 := spliceBytes_toByteArray_eq_writeWord
              (writeWord
                (writeWord
                  (writeWord tinyImmutableBytecode 186
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                  (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                (EVM.Word.ofNat (↑v.owner : Nat))) 245
              (EVM.Word.ofNat (↑v.owner : Nat))
              (by rw [hsize72]; norm_num)
            cases hsp245 : spliceBytes?
                (writeWord
                  (writeWord
                    (writeWord tinyImmutableBytecode 186
                      (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
                    (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
                  (EVM.Word.ofNat (↑v.owner : Nat))) 245
                (UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat))) with
            | none =>
                rw [hsp245] at h245
                cases h245
            | some p245 =>
                rw [hsp245] at h245
                cases h245
                rfl
  · rw [tinyImmutableBytecode_size]
    norm_num

theorem code_eq_patchedRuntime_of_patch {v : TinyImmutables} {code : ByteArray}
    (hcode : patchRuntime tinyImmutableBytecode (patches v) = some code) :
    code = patchedRuntime v := by
  rw [patchRuntime_eq_patchedRuntime] at hcode
  cases hcode
  rfl

theorem patchedRuntime_size (v : TinyImmutables) : (patchedRuntime v).size = 432 := by
  unfold patchedRuntime
  exact writeCascade_size_of_base tinyImmutableBytecode (runtimeWrites v) (base := 432) (out := 432)
    (by native_decide) (by simp [runtimeWrites, WriteGapsOk])
    (by simp [runtimeWrites, writeCascadeSize])

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

theorem patchedRuntime_extract_preserved_len (v : TinyImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 432 read len (runtimeWrites v))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) (hin : read + len ≤ 432) :
    (patchedRuntime v).extract read (read + len) =
      tinyImmutableBytecode.extract read (read + len) := by
  unfold patchedRuntime
  exact writeCascade_extract_preserved_len tinyImmutableBytecode (runtimeWrites v) read len
    (by simpa [tinyImmutableBytecode_size] using hwin) hpos hlen64
    (by change read + len ≤ (patchedRuntime v).size; rw [patchedRuntime_size v]; exact hin)
    (by rw [tinyImmutableBytecode_size]; exact hin)

theorem patchedRuntime_extract'_preserved_len (v : TinyImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 432 read len (runtimeWrites v))
    (hlen64 : read + len < 2 ^ 64) (hin : read + len ≤ 432) :
    (patchedRuntime v).extract' read (read + len) =
      tinyImmutableBytecode.extract' read (read + len) := by
  by_cases hpos : 0 < len
  · unfold ByteArray.extract'
    have hguard : (decide (read < 2 ^ 64) && decide (read + len < 2 ^ 64)) = true := by
      rw [decide_eq_true (by omega : read < 2 ^ 64), decide_eq_true hlen64]
      rfl
    rw [if_pos hguard, if_pos hguard]
    exact patchedRuntime_extract_preserved_len v read len hwin hpos (by omega) hin
  · have hlen0 : len = 0 := by omega
    subst hlen0
    simp [ByteArray.extract']

theorem get?_eq_of_extract_one (a b : ByteArray) (i : Nat) (ha : i < a.size) (hb : i < b.size)
    (h : a.extract i (i + 1) = b.extract i (i + 1)) :
    a.get? i = b.get? i := by
  unfold ByteArray.get?
  simp only [dif_pos ha, dif_pos hb]
  have h0 : (a.extract i (i + 1)).get? 0 = (b.extract i (i + 1)).get? 0 := by rw [h]
  unfold ByteArray.get? at h0
  have hsa : 0 < (a.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  have hsb : 0 < (b.extract i (i + 1)).size := by rw [ByteArray.size_extract]; omega
  simp only [dif_pos hsa, dif_pos hsb] at h0
  have hla : (a.extract i (i + 1)).get 0 hsa = a.get i ha := by
    change (a.extract i (i + 1))[0] = a[i]
    simpa using ByteArray.get_extract (a := a) (start := i) (stop := i + 1) (i := 0) hsa
  have hlb : (b.extract i (i + 1)).get 0 hsb = b.get i hb := by
    change (b.extract i (i + 1))[0] = b[i]
    simpa using ByteArray.get_extract (a := b) (start := i) (stop := i + 1) (i := 0) hsb
  rw [hla, hlb] at h0
  exact h0

theorem patchedRuntime_get?_preserved (v : TinyImmutables) (i : Nat)
    (hwin : WindowDisjointFromWrites 432 i 1 (runtimeWrites v)) (hi : i + 1 ≤ 432) :
    (patchedRuntime v).get? i = tinyImmutableBytecode.get? i := by
  exact get?_eq_of_extract_one (patchedRuntime v) tinyImmutableBytecode i
    (by rw [patchedRuntime_size v]; omega)
    (by rw [tinyImmutableBytecode_size]; omega)
    (patchedRuntime_extract_preserved_len v i 1 hwin (by norm_num) (by norm_num) hi)

theorem decode_eq_of_get?_arg_eq (a b : ByteArray) (pc : UInt256)
    (hget : a.get? pc.toNat = b.get? pc.toNat)
    (harg : ∀ byte instr,
      b.get? pc.toNat = some byte → parseInstr byte = some instr →
      a.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr) =
        b.extract' (pc.toNat + 1) (pc.toNat + 1 + argOnNBytesOfInstr instr)) :
    decode a pc = decode b pc := by
  unfold decode
  rw [hget]
  cases hb : b.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hi : parseInstr byte with
      | none => simp [hi]
      | some instr =>
          simp [hi]
          by_cases hn : argOnNBytesOfInstr instr = 0
          · simp [hn]
          · simp [hn]
            rw [harg byte instr hb hi]

theorem patchedRuntime_decode_preserved (v : TinyImmutables) (pc : UInt256)
    (hgetwin : WindowDisjointFromWrites 432 pc.toNat 1 (runtimeWrites v))
    (hgethi : pc.toNat + 1 ≤ 432)
    (hargwin : ∀ byte instr,
      tinyImmutableBytecode.get? pc.toNat = some byte → parseInstr byte = some instr →
      WindowDisjointFromWrites 432 (pc.toNat + 1) (argOnNBytesOfInstr instr)
        (runtimeWrites v))
    (harghi : ∀ byte instr,
      tinyImmutableBytecode.get? pc.toNat = some byte → parseInstr byte = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 432) :
    decode (patchedRuntime v) pc = decode tinyImmutableBytecode pc := by
  refine decode_eq_of_get?_arg_eq (patchedRuntime v) tinyImmutableBytecode pc
    (patchedRuntime_get?_preserved v pc.toNat hgetwin hgethi) ?_
  intro byte instr hbyte hinstr
  exact patchedRuntime_extract'_preserved_len v (pc.toNat + 1) (argOnNBytesOfInstr instr)
    (hargwin byte instr hbyte hinstr)
    (by have h := harghi byte instr hbyte hinstr; omega)
    (harghi byte instr hbyte hinstr)

theorem patchedRuntime_decode_preserved_of_parse (v : TinyImmutables) (pc : UInt256)
    (byte : UInt8) (instr : Operation)
    (hbyte : tinyImmutableBytecode.get? pc.toNat = some byte)
    (hinstr : parseInstr byte = some instr)
    (hgetwin : WindowDisjointFromWrites 432 pc.toNat 1 (runtimeWrites v))
    (hgethi : pc.toNat + 1 ≤ 432)
    (hargwin :
      WindowDisjointFromWrites 432 (pc.toNat + 1) (argOnNBytesOfInstr instr)
        (runtimeWrites v))
    (harghi : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 432) :
    decode (patchedRuntime v) pc = decode tinyImmutableBytecode pc := by
  refine patchedRuntime_decode_preserved v pc hgetwin hgethi ?_ ?_
  · intro byte' instr' hbyte' hinstr'
    rw [hbyte] at hbyte'
    cases hbyte'
    rw [hinstr] at hinstr'
    cases hinstr'
    exact hargwin
  · intro byte' instr' hbyte' hinstr'
    rw [hbyte] at hbyte'
    cases hbyte'
    rw [hinstr] at hinstr'
    cases hinstr'
    exact harghi

theorem uInt256OfByteArray_toByteArray (w : UInt256) :
    uInt256OfByteArray (UInt256.toByteArray w) = w := by
  rw [uInt256OfByteArray_eq]
  rw [fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

macro "tiny_decode" : tactic =>
  `(tactic|
    (first
      | native_decide
      | rw [patchedRuntime_decode_preserved_of_parse]
        · native_decide
        · native_decide
        · native_decide
        · first
          | native_decide
          | norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size]
        · first
          | native_decide
          | norm_num [UInt256.toNat, UInt256.size]
        · first
          | native_decide
          | norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
              argOnNBytesOfInstr]
        · first
          | native_decide
          | norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr]
      | rw [patchedRuntime_decode_preserved]
        · native_decide
        · first
          | native_decide
          | norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size]
        · first
          | native_decide
          | norm_num [UInt256.toNat, UInt256.size]
        · intro byte instr hbyte hinstr
          first
          | revert hbyte hinstr
            native_decide
          | have hle := argOnNBytesOfInstr_le_32 instr
            simp [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size]
            omega
        · intro byte instr hbyte hinstr
          first
          | revert hbyte hinstr
            native_decide
          | have hle := argOnNBytesOfInstr_le_32 instr
            simp [UInt256.toNat, UInt256.size]
            omega))

theorem patchedRuntime_word72 (v : TinyImmutables) :
    (patchedRuntime v).extract' 72 (72 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat)) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 72 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons, writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord
        (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
        (EVM.wordOfInt (Int.ofNat v.scale.toNat)))
      (base := 432)
      (EVM.Word.ofNat (↑v.owner : Nat))
      [ (245, EVM.Word.ofNat (↑v.owner : Nat)) ] ?_ ?_ ?_
    · rw [writeWord_size]
      · rw [writeWord_size]
        · native_decide
        · rw [tinyImmutableBytecode_size]
          norm_num
      · rw [writeWord_size]
        · rw [tinyImmutableBytecode_size]
          norm_num
        · rw [tinyImmutableBytecode_size]
          norm_num
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 72 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word245 (v : TinyImmutables) :
    (patchedRuntime v).extract' 245 (245 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat (↑v.owner : Nat)) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 245 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord
        (writeWord
          (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 361
          (EVM.wordOfInt (Int.ofNat v.scale.toNat))) 72
        (EVM.Word.ofNat (↑v.owner : Nat)))
      (base := 432)
      (EVM.Word.ofNat (↑v.owner : Nat))
      [] ?_ ?_ ?_
    · rw [writeWord_size]
      · rw [writeWord_size]
        · rw [writeWord_size]
          · native_decide
          · rw [tinyImmutableBytecode_size]
            norm_num
        · rw [writeWord_size]
          · rw [tinyImmutableBytecode_size]
            norm_num
          · rw [tinyImmutableBytecode_size]
            norm_num
      · rw [writeWord_size]
        · rw [writeWord_size]
          · rw [tinyImmutableBytecode_size]
            norm_num
          · rw [tinyImmutableBytecode_size]
            norm_num
        · rw [writeWord_size]
          · rw [tinyImmutableBytecode_size]
            norm_num
          · rw [tinyImmutableBytecode_size]
            norm_num
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 245 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word186 (v : TinyImmutables) :
    (patchedRuntime v).extract' 186 (186 + 32) =
      UInt256.toByteArray (EVM.wordOfInt (Int.ofNat v.scale.toNat)) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 186 32 (by norm_num) (by norm_num)]
  · exact writeCascade_read_word_of_head_of_base tinyImmutableBytecode
      (base := 432)
      (EVM.wordOfInt (Int.ofNat v.scale.toNat))
      [ (361, EVM.wordOfInt (Int.ofNat v.scale.toNat)),
        (72, EVM.Word.ofNat (↑v.owner : Nat)),
        (245, EVM.Word.ofNat (↑v.owner : Nat)) ]
      (by native_decide) (by norm_num) (by simp [WindowDisjointFromWrites])
  · change 186 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word361 (v : TinyImmutables) :
    (patchedRuntime v).extract' 361 (361 + 32) =
      UInt256.toByteArray (EVM.wordOfInt (Int.ofNat v.scale.toNat)) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 361 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord tinyImmutableBytecode 186 (EVM.wordOfInt (Int.ofNat v.scale.toNat)))
      (base := 432)
      (EVM.wordOfInt (Int.ofNat v.scale.toNat))
      [ (72, EVM.Word.ofNat (↑v.owner : Nat)),
        (245, EVM.Word.ofNat (↑v.owner : Nat)) ] ?_ ?_ ?_
    · rw [writeWord_size]
      · native_decide
      · rw [tinyImmutableBytecode_size]
        norm_num
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 361 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem tinyDecodeOwnerWord1 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨71⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.owner : Nat), 32)) := by
  unfold decode
  rw [show (⟨71⟩ : UInt256).toNat = 71 by native_decide]
  rw [patchedRuntime_get?_preserved v 71]
  · have hget : tinyImmutableBytecode.get? 71 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word72 v]
    rw [uInt256OfByteArray_toByteArray]
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem tinyDecodeOwnerWord2 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨244⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat (↑v.owner : Nat), 32)) := by
  unfold decode
  rw [show (⟨244⟩ : UInt256).toNat = 244 by native_decide]
  rw [patchedRuntime_get?_preserved v 244]
  · have hget : tinyImmutableBytecode.get? 244 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word245 v]
    rw [uInt256OfByteArray_toByteArray]
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem tinyDecodeScaleWord1 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨185⟩ =
      some (.Push .PUSH32, some (EVM.wordOfInt (Int.ofNat v.scale.toNat), 32)) := by
  unfold decode
  rw [show (⟨185⟩ : UInt256).toNat = 185 by native_decide]
  rw [patchedRuntime_get?_preserved v 185]
  · have hget : tinyImmutableBytecode.get? 185 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word186 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem tinyDecodeScaleWord2 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨360⟩ =
      some (.Push .PUSH32, some (EVM.wordOfInt (Int.ofNat v.scale.toNat), 32)) := by
  unfold decode
  rw [show (⟨360⟩ : UInt256).toNat = 360 by native_decide]
  rw [patchedRuntime_get?_preserved v 360]
  · have hget : tinyImmutableBytecode.get? 360 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word361 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem tinyDispatch_none_short (v : TinyImmutables) {cd : ByteArray}
    (hcd : cd.size < 4) :
    dispatchMsg (contract v) cd = none := by
  rw [dispatchMsg_eq_dispatchList (contract v) cd]
  refine dispatchList_none_short (transitions v) ?_ hcd
  intro t ht
  simp [transitions] at ht
  rcases ht with ht | ht | ht
  · subst t
    rw [ownerSelectorOf, ownerSelBytes_size]
  · subst t
    rw [quoteSelectorOf, quoteSelBytes_size]
  · subst t
    rw [scaleSelectorOf, scaleSelBytes_size]

theorem tinyDispatch_owner (v : TinyImmutables) {cd : ByteArray}
    (hmatch : (ownerSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (ownerTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := []) (post := [quoteTransition v, scaleTransition v])
    (ti := ownerTransition v) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
  · rw [ownerSelectorOf]
    exact hmatch

theorem tinyDispatch_quote (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hmatch : (quoteSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (quoteTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [ownerTransition v]) (post := [scaleTransition v])
    (ti := quoteTransition v) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    subst t
    rw [ownerSelectorOf]
    exact howner
  · rw [quoteSelectorOf]
    exact hmatch

theorem tinyDispatch_scale (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hquote : (quoteSelBytes == cd.extract 0 4) = false)
    (hmatch : (scaleSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (scaleTransition v) := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [ownerTransition v, quoteTransition v]) (post := [])
    (ti := scaleTransition v) (cd := cd) (by rfl) ?_ ?_ ?_ (by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with ht | ht
    · subst t
      rw [ownerSelectorOf]
      exact howner
    · subst t
      rw [quoteSelectorOf]
      exact hquote
  · rw [scaleSelectorOf]
    exact hmatch

theorem tinyDispatch_none_nomatch (v : TinyImmutables) {cd : ByteArray}
    (howner : (ownerSelBytes == cd.extract 0 4) = false)
    (hquote : (quoteSelBytes == cd.extract 0 4) = false)
    (hscale : (scaleSelBytes == cd.extract 0 4) = false) :
    dispatchMsg (contract v) cd = none := by
  refine dispatchMsg_none_of_all_ne (contract := contract v) (cd := cd) (by rfl) (by rfl) ?_
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with ht | ht | ht
  · subst t
    rw [ownerSelectorOf]
    exact howner
  · subst t
    rw [quoteSelectorOf]
    exact hquote
  · subst t
    rw [scaleSelectorOf]
    exact hscale

theorem tinyOwnerSelector_size {I : ExecutionEnv}
    (hsel : (ownerSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [ownerSelBytes_size, ByteArray.size_extract] at hs
  omega

theorem tinyQuoteSelector_size {I : ExecutionEnv}
    (hsel : (quoteSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [quoteSelBytes_size, ByteArray.size_extract] at hs
  omega

theorem tinyScaleSelector_size {I : ExecutionEnv}
    (hsel : (scaleSelBytes == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  rw [scaleSelBytes_size, ByteArray.size_extract] at hs
  omega

macro "tiny_runtime_bytes" : tactic =>
  `(tactic|
    (try simp [patchedRuntime, runtimeWrites, writeCascade, Reasoning.Theory.writeWord]
     repeat
       rw [write32_eq _ _ _ (by rw [toByteArray_size])
         (by simp [ByteArray.size_append, ByteArray.size_extract])]
     try simp [ByteArray.size_append, ByteArray.size_extract]))

syntax "tiny_decode_at " term "," term "," term "," term : tactic
macro_rules
  | `(tactic| tiny_decode_at $varg, $pc, $byte, $instr) =>
      `(tactic|
        (change decode (patchedRuntime $varg) ($pc : UInt256) = _;
          rw [(patchedRuntime_decode_preserved_of_parse $varg ($pc : UInt256) ($byte : UInt8)
            $instr (by native_decide) (by native_decide)
            (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
            (by norm_num [UInt256.toNat, UInt256.size])
            (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
              argOnNBytesOfInstr])
            (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr]))];
          native_decide))

theorem tinyPushAt8 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨8⟩ = (.PUSH2, (⟨15⟩ : UInt256), 2) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨8⟩ =
    some (.Push .PUSH2, some (⟨15⟩, 2)) by
      tiny_decode_at v, ⟨8⟩, 0x61, (.Push .PUSH2)]

theorem tinyPushAt21 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨21⟩ = (.PUSH2, (⟨63⟩ : UInt256), 2) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨21⟩ =
    some (.Push .PUSH2, some (⟨63⟩, 2)) by
      tiny_decode_at v, ⟨21⟩, 0x61, (.Push .PUSH2)]

theorem tinyPushAt31 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨31⟩ = (.PUSH4, (⟨2376452955⟩ : UInt256), 4) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨31⟩ =
    some (.Push .PUSH4, some (⟨2376452955⟩, 4)) by
      tiny_decode_at v, ⟨31⟩, 0x63, (.Push .PUSH4)]

theorem tinyPushAt37 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨37⟩ = (.PUSH2, (⟨67⟩ : UInt256), 2) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨37⟩ =
    some (.Push .PUSH2, some (⟨67⟩, 2)) by
      tiny_decode_at v, ⟨37⟩, 0x61, (.Push .PUSH2)]

theorem tinyPushAt42 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨42⟩ = (.PUSH4, (⟨3978024812⟩ : UInt256), 4) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨42⟩ =
    some (.Push .PUSH4, some (⟨3978024812⟩, 4)) by
      tiny_decode_at v, ⟨42⟩, 0x63, (.Push .PUSH4)]

theorem tinyPushAt48 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨48⟩ = (.PUSH2, (⟨148⟩ : UInt256), 2) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨48⟩ =
    some (.Push .PUSH2, some (⟨148⟩, 2)) by
      tiny_decode_at v, ⟨48⟩, 0x61, (.Push .PUSH2)]

theorem tinyPushAt53 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨53⟩ = (.PUSH4, (⟨4112390170⟩ : UInt256), 4) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨53⟩ =
    some (.Push .PUSH4, some (⟨4112390170⟩, 4)) by
      tiny_decode_at v, ⟨53⟩, 0x63, (.Push .PUSH4)]

theorem tinyPushAt59 (v : TinyImmutables) :
    pushAt (patchedRuntime v) ⟨59⟩ = (.PUSH2, (⟨181⟩ : UInt256), 2) := by
  unfold pushAt
  rw [show decode (patchedRuntime v) ⟨59⟩ =
    some (.Push .PUSH2, some (⟨181⟩, 2)) by
      tiny_decode_at v, ⟨59⟩, 0x61, (.Push .PUSH2)]

theorem tinyRuntimePrefixWf (v : TinyImmutables) :
    solcDispatchPrefixWellFormed (patchedRuntime v) tinyFirstArmPc := by
  have hguardOp : solcGuardTgtOp (patchedRuntime v) = .PUSH2 := by
    unfold solcGuardTgtOp
    rw [tinyPushAt8 v]
  have hguardTgt : solcGuardTgt (patchedRuntime v) = (⟨15⟩ : UInt256) := by
    unfold solcGuardTgt
    rw [tinyPushAt8 v]
  have hguardWidth : solcGuardTgtWidth (patchedRuntime v) = 2 := by
    unfold solcGuardTgtWidth
    rw [tinyPushAt8 v]
  have hguardJumpi : solcGuardJumpiPc (patchedRuntime v) = (⟨11⟩ : UInt256) := by
    unfold solcGuardJumpiPc
    rw [hguardWidth]
    native_decide
  have hbody : solcDispatchBodyPc (patchedRuntime v) = (⟨17⟩ : UInt256) := by
    unfold solcDispatchBodyPc
    rw [hguardTgt]
    native_decide
  have hrevertPush : solcCalldataRevertPushPc (patchedRuntime v) = (⟨21⟩ : UInt256) := by
    unfold solcCalldataRevertPushPc
    rw [hbody]
    native_decide
  have hrevertOp : solcCalldataRevertTgtOp (patchedRuntime v) = .PUSH2 := by
    unfold solcCalldataRevertTgtOp
    rw [hrevertPush, tinyPushAt21 v]
  have hrevertTgt : solcCalldataRevertTgt (patchedRuntime v) = (⟨63⟩ : UInt256) := by
    unfold solcCalldataRevertTgt
    rw [hrevertPush, tinyPushAt21 v]
  have hrevertWidth : solcCalldataRevertTgtWidth (patchedRuntime v) = 2 := by
    unfold solcCalldataRevertTgtWidth
    rw [hrevertPush, tinyPushAt21 v]
  have hcalldataJumpi : solcCalldataJumpiPc (patchedRuntime v) = (⟨24⟩ : UInt256) := by
    unfold solcCalldataJumpiPc
    rw [hrevertPush, hrevertWidth]
    native_decide
  have hselectorLoad : solcSelectorLoadPc (patchedRuntime v) = (⟨25⟩ : UInt256) := by
    unfold solcSelectorLoadPc
    rw [hcalldataJumpi]
    native_decide
  have hfirstArm : solcFirstArmPcFromPrefix (patchedRuntime v) = tinyFirstArmPc := by
    unfold solcFirstArmPcFromPrefix
    rw [hselectorLoad]
    native_decide
  unfold solcDispatchPrefixWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · tiny_decode_at v, ⟨0⟩, 0x60, (.Push .PUSH1)
  · tiny_decode_at v, ⟨2⟩, 0x60, (.Push .PUSH1)
  · tiny_decode_at v, ⟨4⟩, 0x52, .MSTORE
  · tiny_decode_at v, ⟨5⟩, 0x34, .CALLVALUE
  · tiny_decode_at v, ⟨6⟩, 0x80, .DUP1
  · tiny_decode_at v, ⟨7⟩, 0x15, .ISZERO
  · rw [hguardOp]
    decide
  · rw [hguardOp, hguardTgt, hguardWidth]
    tiny_decode_at v, ⟨8⟩, 0x61, (.Push .PUSH2)
  · rw [hguardJumpi]
    tiny_decode_at v, ⟨11⟩, 0x57, .JUMPI
  · rw [hguardTgt]
    tiny_decode_at v, ⟨15⟩, 0x5b, .JUMPDEST
  · rw [hguardTgt]
    tiny_decode_at v, ⟨16⟩, 0x50, .POP
  · rw [hbody]
    tiny_decode_at v, ⟨17⟩, 0x60, (.Push .PUSH1)
  · rw [hbody]
    tiny_decode_at v, ⟨19⟩, 0x36, .CALLDATASIZE
  · rw [hbody]
    tiny_decode_at v, ⟨20⟩, 0x10, .LT
  · rw [hrevertOp]
    decide
  · rw [hrevertPush, hrevertOp, hrevertTgt, hrevertWidth]
    tiny_decode_at v, ⟨21⟩, 0x61, (.Push .PUSH2)
  · rw [hcalldataJumpi]
    tiny_decode_at v, ⟨24⟩, 0x57, .JUMPI
  · rw [hselectorLoad]
    tiny_decode_at v, ⟨25⟩, 0x5f, .PUSH0
  · rw [hselectorLoad]
    tiny_decode_at v, ⟨26⟩, 0x35, .CALLDATALOAD
  · rw [hselectorLoad]
    tiny_decode_at v, ⟨27⟩, 0x60, (.Push .PUSH1)
  · rw [hselectorLoad]
    tiny_decode_at v, ⟨29⟩, 0x1c, .SHR
  · exact hfirstArm

theorem tinyOwnerArmWellFormed (v : TinyImmutables) :
    armWellFormed (patchedRuntime v) ⟨30⟩ := by
  have hpush4 : selArmPush4Pc (⟨30⟩ : UInt256) = (⟨31⟩ : UInt256) := by native_decide
  have heq : selArmEqPc (⟨30⟩ : UInt256) = (⟨36⟩ : UInt256) := by native_decide
  have hpushTgt : selArmPushTgtPc (⟨30⟩ : UInt256) = (⟨37⟩ : UInt256) := by
    native_decide
  have hjumpi : selArmJumpiPc (⟨30⟩ : UInt256) 2 = (⟨40⟩ : UInt256) := by
    native_decide
  unfold armWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · tiny_decode_at v, ⟨30⟩, 0x80, .DUP1
  · rw [hpush4]
    rw [show armSelNat (patchedRuntime v) (⟨30⟩ : UInt256) = (⟨2376452955⟩ : UInt256) by
      unfold armSelNat
      rw [hpush4, tinyPushAt31 v]]
    tiny_decode_at v, ⟨31⟩, 0x63, (.Push .PUSH4)
  · rw [heq]
    tiny_decode_at v, ⟨36⟩, 0x14, .EQ
  · unfold armTgtOp
    rw [hpushTgt, tinyPushAt37 v]
    decide
  · unfold armTgtOp armTgt armTgtWidth
    rw [hpushTgt, tinyPushAt37 v]
    tiny_decode_at v, ⟨37⟩, 0x61, (.Push .PUSH2)
  · unfold armTgtWidth
    rw [hpushTgt, tinyPushAt37 v, hjumpi]
    tiny_decode_at v, ⟨40⟩, 0x57, .JUMPI

theorem tinyQuoteArmWellFormed (v : TinyImmutables) :
    armWellFormed (patchedRuntime v) ⟨41⟩ := by
  have hpush4 : selArmPush4Pc (⟨41⟩ : UInt256) = (⟨42⟩ : UInt256) := by native_decide
  have heq : selArmEqPc (⟨41⟩ : UInt256) = (⟨47⟩ : UInt256) := by native_decide
  have hpushTgt : selArmPushTgtPc (⟨41⟩ : UInt256) = (⟨48⟩ : UInt256) := by
    native_decide
  have hjumpi : selArmJumpiPc (⟨41⟩ : UInt256) 2 = (⟨51⟩ : UInt256) := by
    native_decide
  unfold armWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · tiny_decode_at v, ⟨41⟩, 0x80, .DUP1
  · rw [hpush4]
    rw [show armSelNat (patchedRuntime v) (⟨41⟩ : UInt256) = (⟨3978024812⟩ : UInt256) by
      unfold armSelNat
      rw [hpush4, tinyPushAt42 v]]
    tiny_decode_at v, ⟨42⟩, 0x63, (.Push .PUSH4)
  · rw [heq]
    tiny_decode_at v, ⟨47⟩, 0x14, .EQ
  · unfold armTgtOp
    rw [hpushTgt, tinyPushAt48 v]
    decide
  · unfold armTgtOp armTgt armTgtWidth
    rw [hpushTgt, tinyPushAt48 v]
    tiny_decode_at v, ⟨48⟩, 0x61, (.Push .PUSH2)
  · unfold armTgtWidth
    rw [hpushTgt, tinyPushAt48 v, hjumpi]
    tiny_decode_at v, ⟨51⟩, 0x57, .JUMPI

theorem tinyScaleArmWellFormed (v : TinyImmutables) :
    armWellFormed (patchedRuntime v) ⟨52⟩ := by
  have hpush4 : selArmPush4Pc (⟨52⟩ : UInt256) = (⟨53⟩ : UInt256) := by native_decide
  have heq : selArmEqPc (⟨52⟩ : UInt256) = (⟨58⟩ : UInt256) := by native_decide
  have hpushTgt : selArmPushTgtPc (⟨52⟩ : UInt256) = (⟨59⟩ : UInt256) := by
    native_decide
  have hjumpi : selArmJumpiPc (⟨52⟩ : UInt256) 2 = (⟨62⟩ : UInt256) := by
    native_decide
  unfold armWellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · tiny_decode_at v, ⟨52⟩, 0x80, .DUP1
  · rw [hpush4]
    rw [show armSelNat (patchedRuntime v) (⟨52⟩ : UInt256) = (⟨4112390170⟩ : UInt256) by
      unfold armSelNat
      rw [hpush4, tinyPushAt53 v]]
    tiny_decode_at v, ⟨53⟩, 0x63, (.Push .PUSH4)
  · rw [heq]
    tiny_decode_at v, ⟨58⟩, 0x14, .EQ
  · unfold armTgtOp
    rw [hpushTgt, tinyPushAt59 v]
    decide
  · unfold armTgtOp armTgt armTgtWidth
    rw [hpushTgt, tinyPushAt59 v]
    tiny_decode_at v, ⟨59⟩, 0x61, (.Push .PUSH2)
  · unfold armTgtWidth
    rw [hpushTgt, tinyPushAt59 v, hjumpi]
    tiny_decode_at v, ⟨62⟩, 0x57, .JUMPI

theorem tinyArmTgtWidth_ownerPc (v : TinyImmutables) :
    armTgtWidth (patchedRuntime v) tinyFirstArmPc = 2 := by
  unfold armTgtWidth
  rw [show selArmPushTgtPc tinyFirstArmPc = (⟨37⟩ : UInt256) by native_decide,
    tinyPushAt37 v]

theorem tinyOwnerArmNextPc (v : TinyImmutables) :
    selArmNextPc tinyFirstArmPc (armTgtWidth (patchedRuntime v) tinyFirstArmPc) = ⟨41⟩ := by
  rw [tinyArmTgtWidth_ownerPc v]
  native_decide

theorem tinyArmTgtWidth_quotePc (v : TinyImmutables) :
    armTgtWidth (patchedRuntime v) ⟨41⟩ = 2 := by
  unfold armTgtWidth
  rw [show selArmPushTgtPc (⟨41⟩ : UInt256) = (⟨48⟩ : UInt256) by native_decide,
    tinyPushAt48 v]

theorem tinyQuoteArmNextPc (v : TinyImmutables) :
    selArmNextPc ⟨41⟩ (armTgtWidth (patchedRuntime v) ⟨41⟩) = ⟨52⟩ := by
  rw [tinyArmTgtWidth_quotePc v]
  native_decide

theorem tinyArmTgtWidth_scalePc (v : TinyImmutables) :
    armTgtWidth (patchedRuntime v) ⟨52⟩ = 2 := by
  unfold armTgtWidth
  rw [show selArmPushTgtPc (⟨52⟩ : UInt256) = (⟨59⟩ : UInt256) by native_decide,
    tinyPushAt59 v]

theorem tinyScaleArmNextPc (v : TinyImmutables) :
    selArmNextPc ⟨52⟩ (armTgtWidth (patchedRuntime v) ⟨52⟩) = ⟨63⟩ := by
  rw [tinyArmTgtWidth_scalePc v]
  native_decide

theorem tinyNthArmPc0 (v : TinyImmutables) :
    nthArmPc (patchedRuntime v) tinyFirstArmPc 0 = tinyFirstArmPc := rfl

theorem tinyNthArmPc1 (v : TinyImmutables) :
    nthArmPc (patchedRuntime v) tinyFirstArmPc 1 = ⟨41⟩ := by
  unfold nthArmPc
  rw [tinyOwnerArmNextPc v]
  rfl

theorem tinyNthArmPc2 (v : TinyImmutables) :
    nthArmPc (patchedRuntime v) tinyFirstArmPc 2 = ⟨52⟩ := by
  unfold nthArmPc
  rw [tinyOwnerArmNextPc v]
  unfold nthArmPc
  rw [tinyQuoteArmNextPc v]
  rfl

theorem tinyArmWellFormed (v : TinyImmutables) :
    ∀ j, j ≤ 2 → armWellFormed (patchedRuntime v)
      (nthArmPc (patchedRuntime v) tinyFirstArmPc j) := by
  intro j hj
  interval_cases j
  · rw [tinyNthArmPc0 v]
    exact tinyOwnerArmWellFormed v
  · rw [tinyNthArmPc1 v]
    exact tinyQuoteArmWellFormed v
  · rw [tinyNthArmPc2 v]
    exact tinyScaleArmWellFormed v

theorem tinyArmTgt_owner (v : TinyImmutables) :
    armTgt (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 0) = ⟨67⟩ := by
  rw [tinyNthArmPc0 v]
  unfold armTgt
  rw [show selArmPushTgtPc tinyFirstArmPc = (⟨37⟩ : UInt256) by native_decide,
    tinyPushAt37 v]

theorem tinyArmTgt_quote (v : TinyImmutables) :
    armTgt (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 1) = ⟨148⟩ := by
  rw [tinyNthArmPc1 v]
  unfold armTgt
  rw [show selArmPushTgtPc (⟨41⟩ : UInt256) = (⟨48⟩ : UInt256) by native_decide,
    tinyPushAt48 v]

theorem tinyArmTgt_scale (v : TinyImmutables) :
    armTgt (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 2) = ⟨181⟩ := by
  rw [tinyNthArmPc2 v]
  unfold armTgt
  rw [show selArmPushTgtPc (⟨52⟩ : UInt256) = (⟨59⟩ : UInt256) by native_decide,
    tinyPushAt59 v]

theorem tinyArmSelNat_owner (v : TinyImmutables) :
    armSelNat (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 0) =
      ⟨2376452955⟩ := by
  rw [tinyNthArmPc0 v]
  unfold armSelNat
  rw [show selArmPush4Pc tinyFirstArmPc = (⟨31⟩ : UInt256) by native_decide,
    tinyPushAt31 v]

theorem tinyArmSelNat_quote (v : TinyImmutables) :
    armSelNat (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 1) =
      ⟨3978024812⟩ := by
  rw [tinyNthArmPc1 v]
  unfold armSelNat
  rw [show selArmPush4Pc (⟨41⟩ : UInt256) = (⟨42⟩ : UInt256) by native_decide,
    tinyPushAt42 v]

theorem tinyArmSelNat_scale (v : TinyImmutables) :
    armSelNat (patchedRuntime v) (nthArmPc (patchedRuntime v) tinyFirstArmPc 2) =
      ⟨4112390170⟩ := by
  rw [tinyNthArmPc2 v]
  unfold armSelNat
  rw [show selArmPush4Pc (⟨52⟩ : UInt256) = (⟨53⟩ : UInt256) by native_decide,
    tinyPushAt53 v]

syntax "tiny_parse_at " term "," term : tactic
macro_rules
  | `(tactic| tiny_parse_at $varg, $pc) =>
      `(tactic|
        (rw [patchedRuntime_get?_preserved $varg ($pc : Nat)
            (by norm_num [runtimeWrites, WindowDisjointFromWrites])
            (by norm_num)];
          native_decide))

syntax "tiny_dj_step " term "," term "," term : tactic
macro_rules
  | `(tactic| tiny_dj_step $varg, $pc, $instr) =>
      `(tactic|
        (rw [D_J_aux_eq_some (patchedRuntime $varg) $pc _ $instr
            (by tiny_parse_at $varg, $pc)];
          simp [EVM.N, argOnNBytesOfInstr]))

theorem tinyPatchedValidJumps (v : TinyImmutables) :
    D_J (patchedRuntime v) 0 =
      #[⟨15⟩, ⟨63⟩, ⟨67⟩, ⟨106⟩, ⟨139⟩, ⟨148⟩, ⟨162⟩, ⟨167⟩, ⟨181⟩, ⟨220⟩,
        ⟨358⟩, ⟨396⟩, ⟨412⟩] := by
  unfold D_J
  tiny_dj_step v, 0, (.Push .PUSH1)
  tiny_dj_step v, 2, (.Push .PUSH1)
  tiny_dj_step v, 4, .MSTORE
  tiny_dj_step v, 5, .CALLVALUE
  tiny_dj_step v, 6, .DUP1
  tiny_dj_step v, 7, .ISZERO
  tiny_dj_step v, 8, (.Push .PUSH2)
  tiny_dj_step v, 11, .JUMPI
  tiny_dj_step v, 12, .PUSH0
  tiny_dj_step v, 13, .PUSH0
  tiny_dj_step v, 14, .REVERT
  tiny_dj_step v, 15, .JUMPDEST
  tiny_dj_step v, 16, .POP
  tiny_dj_step v, 17, (.Push .PUSH1)
  tiny_dj_step v, 19, .CALLDATASIZE
  tiny_dj_step v, 20, .LT
  tiny_dj_step v, 21, (.Push .PUSH2)
  tiny_dj_step v, 24, .JUMPI
  tiny_dj_step v, 25, .PUSH0
  tiny_dj_step v, 26, .CALLDATALOAD
  tiny_dj_step v, 27, (.Push .PUSH1)
  tiny_dj_step v, 29, .SHR
  tiny_dj_step v, 30, .DUP1
  tiny_dj_step v, 31, (.Push .PUSH4)
  tiny_dj_step v, 36, .EQ
  tiny_dj_step v, 37, (.Push .PUSH2)
  tiny_dj_step v, 40, .JUMPI
  tiny_dj_step v, 41, .DUP1
  tiny_dj_step v, 42, (.Push .PUSH4)
  tiny_dj_step v, 47, .EQ
  tiny_dj_step v, 48, (.Push .PUSH2)
  tiny_dj_step v, 51, .JUMPI
  tiny_dj_step v, 52, .DUP1
  tiny_dj_step v, 53, (.Push .PUSH4)
  tiny_dj_step v, 58, .EQ
  tiny_dj_step v, 59, (.Push .PUSH2)
  tiny_dj_step v, 62, .JUMPI
  tiny_dj_step v, 63, .JUMPDEST
  tiny_dj_step v, 64, .PUSH0
  tiny_dj_step v, 65, .PUSH0
  tiny_dj_step v, 66, .REVERT
  tiny_dj_step v, 67, .JUMPDEST
  tiny_dj_step v, 68, (.Push .PUSH2)
  tiny_dj_step v, 71, (.Push .PUSH32)
  tiny_dj_step v, 104, .DUP2
  tiny_dj_step v, 105, .JUMP
  tiny_dj_step v, 106, .JUMPDEST
  tiny_dj_step v, 107, (.Push .PUSH1)
  tiny_dj_step v, 109, .MLOAD
  tiny_dj_step v, 110, (.Push .PUSH20)
  tiny_dj_step v, 131, .SWAP1
  tiny_dj_step v, 132, .SWAP2
  tiny_dj_step v, 133, .AND
  tiny_dj_step v, 134, .DUP2
  tiny_dj_step v, 135, .MSTORE
  tiny_dj_step v, 136, (.Push .PUSH1)
  tiny_dj_step v, 138, .ADD
  tiny_dj_step v, 139, .JUMPDEST
  tiny_dj_step v, 140, (.Push .PUSH1)
  tiny_dj_step v, 142, .MLOAD
  tiny_dj_step v, 143, .DUP1
  tiny_dj_step v, 144, .SWAP2
  tiny_dj_step v, 145, .SUB
  tiny_dj_step v, 146, .SWAP1
  tiny_dj_step v, 147, .RETURN
  tiny_dj_step v, 148, .JUMPDEST
  tiny_dj_step v, 149, (.Push .PUSH2)
  tiny_dj_step v, 152, (.Push .PUSH2)
  tiny_dj_step v, 155, .CALLDATASIZE
  tiny_dj_step v, 156, (.Push .PUSH1)
  tiny_dj_step v, 158, (.Push .PUSH2)
  tiny_dj_step v, 161, .JUMP
  tiny_dj_step v, 162, .JUMPDEST
  tiny_dj_step v, 163, (.Push .PUSH2)
  tiny_dj_step v, 166, .JUMP
  tiny_dj_step v, 167, .JUMPDEST
  tiny_dj_step v, 168, (.Push .PUSH1)
  tiny_dj_step v, 170, .MLOAD
  tiny_dj_step v, 171, .SWAP1
  tiny_dj_step v, 172, .DUP2
  tiny_dj_step v, 173, .MSTORE
  tiny_dj_step v, 174, (.Push .PUSH1)
  tiny_dj_step v, 176, .ADD
  tiny_dj_step v, 177, (.Push .PUSH2)
  tiny_dj_step v, 180, .JUMP
  tiny_dj_step v, 181, .JUMPDEST
  tiny_dj_step v, 182, (.Push .PUSH2)
  tiny_dj_step v, 185, (.Push .PUSH32)
  tiny_dj_step v, 218, .DUP2
  tiny_dj_step v, 219, .JUMP
  tiny_dj_step v, 220, .JUMPDEST
  tiny_dj_step v, 221, .PUSH0
  tiny_dj_step v, 222, .CALLER
  tiny_dj_step v, 223, (.Push .PUSH20)
  tiny_dj_step v, 244, (.Push .PUSH32)
  tiny_dj_step v, 277, .AND
  tiny_dj_step v, 278, .EQ
  tiny_dj_step v, 279, (.Push .PUSH2)
  tiny_dj_step v, 282, .JUMPI
  tiny_dj_step v, 283, (.Push .PUSH1)
  tiny_dj_step v, 285, .MLOAD
  tiny_dj_step v, 286, (.Push .PUSH3)
  tiny_dj_step v, 290, (.Push .PUSH1)
  tiny_dj_step v, 292, .SHL
  tiny_dj_step v, 293, .DUP2
  tiny_dj_step v, 294, .MSTORE
  tiny_dj_step v, 295, (.Push .PUSH1)
  tiny_dj_step v, 297, (.Push .PUSH1)
  tiny_dj_step v, 299, .DUP3
  tiny_dj_step v, 300, .ADD
  tiny_dj_step v, 301, .MSTORE
  tiny_dj_step v, 302, (.Push .PUSH1)
  tiny_dj_step v, 304, (.Push .PUSH1)
  tiny_dj_step v, 306, .DUP3
  tiny_dj_step v, 307, .ADD
  tiny_dj_step v, 308, .MSTORE
  tiny_dj_step v, 309, (.Push .PUSH32)
  tiny_dj_step v, 342, (.Push .PUSH1)
  tiny_dj_step v, 344, .DUP3
  tiny_dj_step v, 345, .ADD
  tiny_dj_step v, 346, .MSTORE
  tiny_dj_step v, 347, (.Push .PUSH1)
  tiny_dj_step v, 349, .ADD
  tiny_dj_step v, 350, (.Push .PUSH1)
  tiny_dj_step v, 352, .MLOAD
  tiny_dj_step v, 353, .DUP1
  tiny_dj_step v, 354, .SWAP2
  tiny_dj_step v, 355, .SUB
  tiny_dj_step v, 356, .SWAP1
  tiny_dj_step v, 357, .REVERT
  tiny_dj_step v, 358, .JUMPDEST
  tiny_dj_step v, 359, .POP
  tiny_dj_step v, 360, (.Push .PUSH32)
  tiny_dj_step v, 393, .MUL
  tiny_dj_step v, 394, .SWAP1
  tiny_dj_step v, 395, .JUMP
  tiny_dj_step v, 396, .JUMPDEST
  tiny_dj_step v, 397, .PUSH0
  tiny_dj_step v, 398, (.Push .PUSH1)
  tiny_dj_step v, 400, .DUP3
  tiny_dj_step v, 401, .DUP5
  tiny_dj_step v, 402, .SUB
  tiny_dj_step v, 403, .SLT
  tiny_dj_step v, 404, .ISZERO
  tiny_dj_step v, 405, (.Push .PUSH2)
  tiny_dj_step v, 408, .JUMPI
  tiny_dj_step v, 409, .PUSH0
  tiny_dj_step v, 410, .PUSH0
  tiny_dj_step v, 411, .REVERT
  tiny_dj_step v, 412, .JUMPDEST
  tiny_dj_step v, 413, .POP
  tiny_dj_step v, 414, .CALLDATALOAD
  tiny_dj_step v, 415, .SWAP2
  tiny_dj_step v, 416, .SWAP1
  tiny_dj_step v, 417, .POP
  tiny_dj_step v, 418, .JUMP
  tiny_dj_step v, 419, .INVALID
  tiny_dj_step v, 420, .LOG1
  tiny_dj_step v, 421, (.Push .PUSH5)
  tiny_dj_step v, 427, .STOP
  tiny_dj_step v, 428, .ADDMOD
  tiny_dj_step v, 429, .INVALID
  tiny_dj_step v, 430, .STOP
  tiny_dj_step v, 431, .EXP
  rw [D_J_aux_ge_size (patchedRuntime v) 432 _ (by rw [patchedRuntime_size v])]
  native_decide

theorem tinyContains15 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨15⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains63 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨63⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains67 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨67⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains106 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨106⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains139 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨139⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains148 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨148⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains162 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨162⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains167 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨167⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains181 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨181⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains220 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨220⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains358 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨358⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains396 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨396⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyContains412 (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains ⟨412⟩ = true := by
  rw [tinyPatchedValidJumps v]
  native_decide

theorem tinyOwnerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2376452955⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (ownerSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x8d 0xa5 0xcb 0x5b ⟨2376452955⟩ (by decide)

theorem tinyQuoteEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨3978024812⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (quoteSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xed 0x1b 0xd7 0x6c ⟨3978024812⟩ (by decide)

theorem tinyScaleEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨4112390170⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if (scaleSelBytes == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xf5 0x1e 0x18 0x1a ⟨4112390170⟩ (by decide)

theorem tinySolcGuardTgt (v : TinyImmutables) :
    solcGuardTgt (patchedRuntime v) = ⟨15⟩ := by
  unfold solcGuardTgt pushAt
  rw [show decode (patchedRuntime v) ⟨8⟩ =
    some (.Push .PUSH2, some (⟨15⟩, 2)) by tiny_decode]

theorem tinyGuardJd (v : TinyImmutables) :
    (D_J (patchedRuntime v) 0).contains (solcGuardTgt (patchedRuntime v)) = true := by
  rw [tinySolcGuardTgt]
  exact tinyContains15 v

theorem tinyArmSelNat_ownerPc (v : TinyImmutables) :
    armSelNat (patchedRuntime v) tinyFirstArmPc = ⟨2376452955⟩ := by
  unfold armSelNat pushAt selArmPush4Pc
  have hpc : tinyFirstArmPc + ⟨1⟩ = (⟨31⟩ : UInt256) := by native_decide
  rw [hpc]
  rw [show decode (patchedRuntime v) ⟨31⟩ =
    some (.Push .PUSH4, some (⟨2376452955⟩, 4)) by tiny_decode]

theorem tinyArmSelNat_quotePc (v : TinyImmutables) :
    armSelNat (patchedRuntime v) ⟨41⟩ = ⟨3978024812⟩ := by
  unfold armSelNat pushAt selArmPush4Pc
  have hpc : (⟨41⟩ : UInt256) + ⟨1⟩ = (⟨42⟩ : UInt256) := by native_decide
  rw [hpc]
  rw [show decode (patchedRuntime v) ⟨42⟩ =
    some (.Push .PUSH4, some (⟨3978024812⟩, 4)) by
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨42⟩ : UInt256) 0x63
        (.Push .PUSH4) (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide]

theorem tinyArmSelNat_scalePc (v : TinyImmutables) :
    armSelNat (patchedRuntime v) ⟨52⟩ = ⟨4112390170⟩ := by
  unfold armSelNat pushAt selArmPush4Pc
  have hpc : (⟨52⟩ : UInt256) + ⟨1⟩ = (⟨53⟩ : UInt256) := by native_decide
  rw [hpc]
  rw [show decode (patchedRuntime v) ⟨53⟩ =
    some (.Push .PUSH4, some (⟨4112390170⟩, 4)) by
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨53⟩ : UInt256) 0x63
        (.Push .PUSH4) (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide]

theorem tinyDecodeJumpdest63 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨63⟩ = some (.JUMPDEST, .none) := by
  have hpres := patchedRuntime_decode_preserved_of_parse v (⟨63⟩ : UInt256) 0x5b
    .JUMPDEST (by native_decide) (by native_decide)
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
    (by norm_num [UInt256.toNat, UInt256.size])
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
      argOnNBytesOfInstr])
    (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
  rw [hpres]
  native_decide

theorem tinyDecodePush0_64 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨64⟩ = some (.PUSH0, .none) := by
  have hpres := patchedRuntime_decode_preserved_of_parse v (⟨64⟩ : UInt256) 0x5f
    .PUSH0 (by native_decide) (by native_decide)
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
    (by norm_num [UInt256.toNat, UInt256.size])
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
      argOnNBytesOfInstr])
    (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
  rw [hpres]
  native_decide

theorem tinyDecodePush0_65 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨65⟩ = some (.PUSH0, .none) := by
  have hpres := patchedRuntime_decode_preserved_of_parse v (⟨65⟩ : UInt256) 0x5f
    .PUSH0 (by native_decide) (by native_decide)
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
    (by norm_num [UInt256.toNat, UInt256.size])
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
      argOnNBytesOfInstr])
    (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
  rw [hpres]
  native_decide

theorem tinyDecodeRevert66 (v : TinyImmutables) :
    decode (patchedRuntime v) ⟨66⟩ = some (.REVERT, .none) := by
  have hpres := patchedRuntime_decode_preserved_of_parse v (⟨66⟩ : UInt256) 0xfd
    .REVERT (by native_decide) (by native_decide)
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
    (by norm_num [UInt256.toNat, UInt256.size])
    (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
      argOnNBytesOfInstr])
    (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
  rw [hpres]
  native_decide

theorem tinyReachOwnerBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨67⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := tinyFirstArmPc) (bodyPC := ⟨67⟩) (i := 0)
    hcode hwv hsz hsize (tinyRuntimePrefixWf v) (tinyGuardJd v)
    (fun j hj => by rw [Nat.le_zero.mp hj]; exact tinyOwnerArmWellFormed v)
    (fun j hj => absurd hj (by omega))
    (by
      show UInt256.eq (armSelNat (patchedRuntime v)
          (nthArmPc (patchedRuntime v) tinyFirstArmPc 0)) (solcSelectorWord I) ≠ ⟨0⟩
      rw [tinyArmSelNat_owner v, solcSelectorWord, tinyOwnerEvmSelector hsz, if_pos howner]
      decide)
    (tinyContains67 v) (tinyArmTgt_owner v)

theorem tinyReachQuoteBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨148⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := tinyFirstArmPc) (bodyPC := ⟨148⟩) (i := 1)
    hcode hwv hsz hsize (tinyRuntimePrefixWf v) (tinyGuardJd v)
    (fun j hj => tinyArmWellFormed v j (by omega))
    (by
      intro j hj
      interval_cases j
      show UInt256.eq (armSelNat (patchedRuntime v)
          (nthArmPc (patchedRuntime v) tinyFirstArmPc 0)) (solcSelectorWord I) = ⟨0⟩
      rw [tinyArmSelNat_owner v, solcSelectorWord, tinyOwnerEvmSelector hsz]
      simp [howner])
    (by
      show UInt256.eq (armSelNat (patchedRuntime v)
          (nthArmPc (patchedRuntime v) tinyFirstArmPc 1)) (solcSelectorWord I) ≠ ⟨0⟩
      rw [tinyArmSelNat_quote v, solcSelectorWord, tinyQuoteEvmSelector hsz, if_pos hquote]
      decide)
    (tinyContains148 v) (tinyArmTgt_quote v)

theorem tinyReachScaleBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hscale : (scaleSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨181⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := tinyFirstArmPc) (bodyPC := ⟨181⟩) (i := 2)
    hcode hwv hsz hsize (tinyRuntimePrefixWf v) (tinyGuardJd v)
    (fun j hj => tinyArmWellFormed v j hj)
    (by
      intro j hj
      interval_cases j
      · show UInt256.eq (armSelNat (patchedRuntime v)
            (nthArmPc (patchedRuntime v) tinyFirstArmPc 0)) (solcSelectorWord I) = ⟨0⟩
        rw [tinyArmSelNat_owner v, solcSelectorWord, tinyOwnerEvmSelector hsz]
        simp [howner]
      · show UInt256.eq (armSelNat (patchedRuntime v)
            (nthArmPc (patchedRuntime v) tinyFirstArmPc 1)) (solcSelectorWord I) = ⟨0⟩
        rw [tinyArmSelNat_quote v, solcSelectorWord, tinyQuoteEvmSelector hsz]
        simp [hquote])
    (by
      show UInt256.eq (armSelNat (patchedRuntime v)
          (nthArmPc (patchedRuntime v) tinyFirstArmPc 2)) (solcSelectorWord I) ≠ ⟨0⟩
      rw [tinyArmSelNat_scale v, solcSelectorWord, tinyScaleEvmSelector hsz, if_pos hscale]
      decide)
    (tinyContains181 v) (tinyArmTgt_scale v)

theorem tinyX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode
    (by tiny_decode) (by tiny_decode) (by tiny_decode) (by tiny_decode) (by tiny_decode)
    (by tiny_decode)
  exact solcGuardCallvalueNonzeroRevert
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2) h0 hwv (by decide)
    (by
      change decode (patchedRuntime v) (⟨8⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨15⟩, 2))
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨11⟩ : UInt256) = some (.JUMPI, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨12⟩ : UInt256) = some (.PUSH0, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨13⟩ : UInt256) = some (.PUSH0, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨14⟩ : UInt256) = some (.REVERT, .none)
      tiny_decode)

theorem tinyX_short {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode
    (by tiny_decode) (by tiny_decode) (by tiny_decode) (by tiny_decode) (by tiny_decode)
    (by tiny_decode)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2) h0 hwv (by decide)
    (by
      change decode (patchedRuntime v) (⟨8⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨15⟩, 2))
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨11⟩ : UInt256) = some (.JUMPI, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨15⟩ : UInt256) = some (.JUMPDEST, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨16⟩ : UInt256) = some (.POP, .none)
      tiny_decode)
    (tinyContains15 v)
  exact solcCalldataShortRevert
    (bodyPc := (⟨17⟩ : UInt256)) (rtgt := (⟨63⟩ : UInt256))
    (opR := .PUSH2) (wR := 2) h1 hsz
    (by
      change decode (patchedRuntime v) (⟨17⟩ : UInt256) =
        some (.Push .PUSH1, some (⟨4⟩, 1))
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨19⟩ : UInt256) = some (.CALLDATASIZE, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨20⟩ : UInt256) = some (.LT, .none)
      tiny_decode)
    (by decide)
    (by
      change decode (patchedRuntime v) (⟨21⟩ : UInt256) =
        some (.Push .PUSH2, some (⟨63⟩, 2))
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨24⟩ : UInt256) = some (.JUMPI, .none)
      tiny_decode)
    (by
      change decode (patchedRuntime v) (⟨63⟩ : UInt256) = some (.JUMPDEST, .none)
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨63⟩ : UInt256) 0x5b
        .JUMPDEST (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide)
    (tinyContains63 v)
    (by
      change decode (patchedRuntime v) (⟨64⟩ : UInt256) = some (.PUSH0, .none)
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨64⟩ : UInt256) 0x5f
        .PUSH0 (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide)
    (by
      change decode (patchedRuntime v) (⟨65⟩ : UInt256) = some (.PUSH0, .none)
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨65⟩ : UInt256) 0x5f
        .PUSH0 (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide)
    (by
      change decode (patchedRuntime v) (⟨66⟩ : UInt256) = some (.REVERT, .none)
      have hpres := patchedRuntime_decode_preserved_of_parse v (⟨66⟩ : UInt256) 0xfd
        .REVERT (by native_decide) (by native_decide)
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size])
        (by norm_num [UInt256.toNat, UInt256.size])
        (by norm_num [runtimeWrites, WindowDisjointFromWrites, UInt256.toNat, UInt256.size,
          argOnNBytesOfInstr])
        (by norm_num [UInt256.toNat, UInt256.size, argOnNBytesOfInstr])
      rw [hpres]
      native_decide)

set_option maxHeartbeats 1000000 in
theorem tinyX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256} (v : TinyImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (howner : (ownerSelBytes == I.calldata.extract 0 4) = false)
    (hquote : (quoteSelBytes == I.calldata.extract 0 4) = false)
    (hscale : (scaleSelBytes == I.calldata.extract 0 4) = false) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k30, C30, h30⟩ := solcDispatchReachSelector (firstPc := tinyFirstArmPc)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (code := patchedRuntime v)
    hcode hwv hsz hsize (tinyRuntimePrefixWf v) (tinyGuardJd v)
  have h41 := h30.selectorArmNotTakenAuto (tinyOwnerArmWellFormed v)
    (by
      show UInt256.eq (armSelNat (patchedRuntime v) tinyFirstArmPc) (solcSelectorWord I) =
          ⟨0⟩
      rw [tinyArmSelNat_ownerPc v, solcSelectorWord, tinyOwnerEvmSelector hsz]
      simp [howner])
    (by simp)
  have h41' : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨41⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k30 + 5) (C30 + 22) := by
    simpa [tinyOwnerArmNextPc v] using h41
  have h52 := h41'.selectorArmNotTakenAuto (tinyQuoteArmWellFormed v)
    (by
      show UInt256.eq (armSelNat (patchedRuntime v) ⟨41⟩) (solcSelectorWord I) =
          ⟨0⟩
      rw [tinyArmSelNat_quotePc v, solcSelectorWord, tinyQuoteEvmSelector hsz]
      simp [hquote])
    (by simp)
  have h52' : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨52⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) ((k30 + 5) + 5) ((C30 + 22) + 22) := by
    simpa [tinyQuoteArmNextPc v] using h52
  have h63 := h52'.selectorArmNotTakenAuto (tinyScaleArmWellFormed v)
    (by
      show UInt256.eq (armSelNat (patchedRuntime v) ⟨52⟩) (solcSelectorWord I) =
          ⟨0⟩
      rw [tinyArmSelNat_scalePc v, solcSelectorWord, tinyScaleEvmSelector hsz]
      simp [hscale])
    (by simp)
  have h63' : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨63⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (((k30 + 5) + 5) + 5) (((C30 + 22) + 22) + 22) := by
    simpa [tinyScaleArmNextPc v] using h63
  have h64 := h63'.jumpdest (tinyDecodeJumpdest63 v) (by simp)
  exact h64.revertStub (tinyDecodePush0_64 v) (tinyDecodePush0_65 v)
    (tinyDecodeRevert66 v) (by simp)

theorem tinyOwnerWord_canonical (v : TinyImmutables) :
    (EVM.Word.ofNat (↑v.owner : Nat)).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.owner.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change v.owner.val < AccountAddress.size
    exact v.owner.isLt
  · exact lt_of_lt_of_le v.owner.isLt (by decide)

theorem tinyOwnerWord_toNat (v : TinyImmutables) :
    (EVM.Word.ofNat (↑v.owner : Nat)).toNat = (↑v.owner : Nat) := by
  change (UInt256.ofNat v.owner.val).toNat = v.owner.val
  rw [UInt256.toNat_ofNat_of_lt]
  exact lt_of_lt_of_le v.owner.isLt (by decide)

theorem tinyOwnerWord_clean (v : TinyImmutables) :
    UInt256.land (EVM.Word.ofNat (↑v.owner : Nat)) solcAddrMask =
      EVM.Word.ofNat (↑v.owner : Nat) :=
  solcAddrMask_clean (tinyOwnerWord_canonical v)

set_option maxHeartbeats 1000000 in
theorem RD.tinyReturnWord167 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {v : TinyImmutables} {val : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (patchedRuntime v) ee g s0 ⟨167⟩ (val :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret (patchedRuntime v) g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    raw jumpdest (by tiny_decode_at v, ⟨167⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨168⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by tiny_decode_at v, ⟨170⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨171⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by tiny_decode_at v, ⟨172⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5)
      (by tiny_decode_at v, ⟨173⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by tiny_decode_at v, ⟨174⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨176⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨139⟩ (by tiny_decode_at v, ⟨177⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by tiny_decode_at v, ⟨180⟩, 0x56, .JUMP) (tinyContains139 v) (by evm_ov),
    raw jumpdest (by tiny_decode_at v, ⟨139⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨140⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by tiny_decode_at v, ⟨142⟩, 0x51, .MLOAD)
      mem_cost (solcReturnMem_mload64 val) (by decide) (by evm_ov),
    raw dup1 (by tiny_decode_at v, ⟨143⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by tiny_decode_at v, ⟨144⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by tiny_decode_at v, ⟨145⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨146⟩, 0x90, .SWAP1) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by tiny_decode_at v, ⟨147⟩, 0xf3, .RETURN)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        simpa using solcReturnMem_read128 val)
      (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.tinyReturnAddress106 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : Nat}
    {v : TinyImmutables} {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD (patchedRuntime v) ee g s0 ⟨106⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret (patchedRuntime v) g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  exact evm_run h with [
    raw jumpdest (by tiny_decode_at v, ⟨106⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨107⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by tiny_decode_at v, ⟨109⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push20 solcAddrMask (by tiny_decode_at v, ⟨110⟩, 0x73, (.Push .PUSH20))
      (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨131⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by tiny_decode_at v, ⟨132⟩, 0x91, .SWAP2) (by evm_ov),
    raw and (by tiny_decode_at v, ⟨133⟩, 0x16, .AND) (by evm_ov),
    raw dup2 (by tiny_decode_at v, ⟨134⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by tiny_decode_at v, ⟨135⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by tiny_decode_at v, ⟨136⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by tiny_decode_at v, ⟨138⟩, 0x01, .ADD) (by evm_ov),
    raw jumpdest (by tiny_decode_at v, ⟨139⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by tiny_decode_at v, ⟨140⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by tiny_decode_at v, ⟨142⟩, 0x51, .MLOAD)
      mem_cost (solcReturnMem_mload64 (UInt256.land val solcAddrMask)) (by decide)
      (by evm_ov),
    raw dup1 (by tiny_decode_at v, ⟨143⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by tiny_decode_at v, ⟨144⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by tiny_decode_at v, ⟨145⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by tiny_decode_at v, ⟨146⟩, 0x90, .SWAP1) (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val solcAddrMask))
      (by tiny_decode_at v, ⟨147⟩, 0xf3, .RETURN)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        simpa using solcReturnMem_read128 (UInt256.land val solcAddrMask))
      (by evm_ov)]

end TinyImmutable
