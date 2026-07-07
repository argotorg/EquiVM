import Benchmarks.EAS.Attester.Trusted
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.MemCascade
import Reasoning.Solc
import Reasoning.SolmBody
import Solm.Equiv

/-!
# Shared Attester proof helpers
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

set_option maxRecDepth 10000

abbrev attesterFirstArmPc : UInt256 := ⟨30⟩

@[simp] theorem wordBytesBEArray_size (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray).size = 32 := by
  simpa using word_toBytesBE_toByteArray_size w

@[simp] theorem wordBytesBEArray_eq_toByteArray (w : UInt256) :
    ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray) = UInt256.toByteArray w := by
  apply ByteArray.ext
  have h := congrArg ByteArray.data (word_toBytesBE_toByteArray_eq_toByteArray w)
  simpa using h

@[simp] theorem attesterBytecode_size : attesterBytecode.size = 3186 := by
  native_decide +revert

@[simp] theorem attesterCreationBytecode_size : attesterCreationBytecode.size = 3371 := by
  native_decide +revert

def runtimeWrites (v : AttesterImmutables) : List (Nat × UInt256) :=
  [ (722, EVM.Word.ofNat v.eas.toNat),
    (1465, EVM.Word.ofNat v.eas.toNat),
    (1598, EVM.Word.ofNat v.eas.toNat),
    (1939, EVM.Word.ofNat v.eas.toNat) ]

noncomputable def patchedRuntime (v : AttesterImmutables) : ByteArray :=
  writeCascade attesterBytecode (runtimeWrites v)

theorem spliceBytes_toByteArray_eq_writeWord (mem : ByteArray) (off : Nat) (w : UInt256)
    (h : off + 32 ≤ mem.size) :
    spliceBytes? mem off (UInt256.toByteArray w) = some (writeWord mem off w) := by
  unfold spliceBytes? Reasoning.Theory.writeWord
  rw [toByteArray_size, if_pos h]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

theorem patchRuntime_eq_patchedRuntime (v : AttesterImmutables) :
    patchRuntime attesterBytecode (patches v) = some (patchedRuntime v) := by
  simp [patchedRuntime, patchRuntime, patches, patchesFrom, offsets, immValues, wordBytes?,
    valueToWord, List.lookup_cons, runtimeWrites, writeCascade]
  rw [spliceBytes_toByteArray_eq_writeWord attesterBytecode 722]
  · simp
    have hgap722 : 722 - attesterBytecode.size < USize.size := by
      rw [attesterBytecode_size]
      norm_num
    have hsize722 :
        (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
      rw [writeWord_size _ _ _ hgap722]
      rw [attesterBytecode_size]
      norm_num
    have h1465 := spliceBytes_toByteArray_eq_writeWord
      (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
      (EVM.Word.ofNat v.eas.toNat)
      (by rw [hsize722]; norm_num)
    cases hsp1465 : spliceBytes?
        (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
        (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat)) with
    | none =>
        rw [hsp1465] at h1465
        cases h1465
    | some p1465 =>
        rw [hsp1465] at h1465
        cases h1465
        have hgap1465 :
            1465 - (writeWord attesterBytecode 722
              (EVM.Word.ofNat v.eas.toNat)).size < USize.size := by
          rw [hsize722]
          norm_num
        have hsize1465 :
            (writeWord
              (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
              (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
          rw [writeWord_size _ _ _ hgap1465]
          rw [hsize722]
          norm_num
        have h1598 := spliceBytes_toByteArray_eq_writeWord
          (writeWord
            (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
            (EVM.Word.ofNat v.eas.toNat)) 1598
          (EVM.Word.ofNat v.eas.toNat)
          (by rw [hsize1465]; norm_num)
        cases hsp1598 : spliceBytes?
            (writeWord
              (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
              (EVM.Word.ofNat v.eas.toNat)) 1598
            (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat)) with
        | none =>
            rw [hsp1598] at h1598
            cases h1598
        | some p1598 =>
            rw [hsp1598] at h1598
            cases h1598
            have hgap1598 :
                1598 - (writeWord
                  (writeWord attesterBytecode 722
                    (EVM.Word.ofNat v.eas.toNat)) 1465
                  (EVM.Word.ofNat v.eas.toNat)).size < USize.size := by
              rw [hsize1465]
              norm_num
            have hsize1598 :
                (writeWord
                  (writeWord
                    (writeWord attesterBytecode 722
                      (EVM.Word.ofNat v.eas.toNat)) 1465
                    (EVM.Word.ofNat v.eas.toNat)) 1598
                  (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
              rw [writeWord_size _ _ _ hgap1598]
              rw [hsize1465]
              norm_num
            have h1939 := spliceBytes_toByteArray_eq_writeWord
              (writeWord
                (writeWord
                  (writeWord attesterBytecode 722
                    (EVM.Word.ofNat v.eas.toNat)) 1465
                  (EVM.Word.ofNat v.eas.toNat)) 1598
                (EVM.Word.ofNat v.eas.toNat)) 1939
              (EVM.Word.ofNat v.eas.toNat)
              (by rw [hsize1598]; norm_num)
            cases hsp1939 : spliceBytes?
                (writeWord
                  (writeWord
                    (writeWord attesterBytecode 722
                      (EVM.Word.ofNat v.eas.toNat)) 1465
                    (EVM.Word.ofNat v.eas.toNat)) 1598
                  (EVM.Word.ofNat v.eas.toNat)) 1939
                (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat)) with
            | none =>
                rw [hsp1939] at h1939
                cases h1939
            | some p1939 =>
                rw [hsp1939] at h1939
                cases h1939
                change
                  (spliceBytes?
                    (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
                    (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat))).bind
                    (fun init =>
                      (spliceBytes? init 1598
                        (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat))).bind
                        (fun init =>
                          spliceBytes? init 1939
                            (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat)))) =
                    some
                      (writeWord
                        (writeWord
                          (writeWord
                            (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
                            (EVM.Word.ofNat v.eas.toNat))
                          1598 (EVM.Word.ofNat v.eas.toNat))
                        1939 (EVM.Word.ofNat v.eas.toNat))
                rw [hsp1465]
                simp only [Option.bind]
                rw [hsp1598]
                change
                  spliceBytes?
                    (writeWord
                      (writeWord
                        (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
                        (EVM.Word.ofNat v.eas.toNat))
                      1598 (EVM.Word.ofNat v.eas.toNat))
                    1939 (UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat)) =
                    some
                      (writeWord
                        (writeWord
                          (writeWord
                            (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
                            (EVM.Word.ofNat v.eas.toNat))
                          1598 (EVM.Word.ofNat v.eas.toNat))
                        1939 (EVM.Word.ofNat v.eas.toNat))
                rw [hsp1939]
  · rw [attesterBytecode_size]
    norm_num

theorem code_eq_patchedRuntime_of_patch {v : AttesterImmutables} {code : ByteArray}
    (hcode : patchRuntime attesterBytecode (patches v) = some code) :
    code = patchedRuntime v := by
  rw [patchRuntime_eq_patchedRuntime] at hcode
  cases hcode
  rfl

theorem patchedRuntime_size (v : AttesterImmutables) : (patchedRuntime v).size = 3186 := by
  unfold patchedRuntime
  exact writeCascade_size_of_base attesterBytecode (runtimeWrites v) (base := 3186) (out := 3186)
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

theorem patchedRuntime_extract_preserved_len (v : AttesterImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 3186 read len (runtimeWrites v))
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) (hin : read + len ≤ 3186) :
    (patchedRuntime v).extract read (read + len) =
      attesterBytecode.extract read (read + len) := by
  unfold patchedRuntime
  exact writeCascade_extract_preserved_len attesterBytecode (runtimeWrites v) read len
    (by simpa [attesterBytecode_size] using hwin) hpos hlen64
    (by change read + len ≤ (patchedRuntime v).size; rw [patchedRuntime_size v]; exact hin)
    (by rw [attesterBytecode_size]; exact hin)

theorem patchedRuntime_extract'_preserved_len (v : AttesterImmutables) (read len : Nat)
    (hwin : WindowDisjointFromWrites 3186 read len (runtimeWrites v))
    (hlen64 : read + len < 2 ^ 64) (hin : read + len ≤ 3186) :
    (patchedRuntime v).extract' read (read + len) =
      attesterBytecode.extract' read (read + len) := by
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

theorem get?_eq_of_extract_one (a b : ByteArray) (i : Nat)
    (ha : i < a.size) (hb : i < b.size)
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

theorem patchedRuntime_get?_preserved (v : AttesterImmutables) (i : Nat)
    (hwin : WindowDisjointFromWrites 3186 i 1 (runtimeWrites v)) (hi : i + 1 ≤ 3186) :
    (patchedRuntime v).get? i = attesterBytecode.get? i := by
  exact get?_eq_of_extract_one (patchedRuntime v) attesterBytecode i
    (by rw [patchedRuntime_size v]; omega)
    (by rw [attesterBytecode_size]; omega)
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

theorem patchedRuntime_decode_preserved (v : AttesterImmutables) (pc : UInt256)
    (hgetwin : WindowDisjointFromWrites 3186 pc.toNat 1 (runtimeWrites v))
    (hgethi : pc.toNat + 1 ≤ 3186)
    (hargwin : ∀ byte instr,
      attesterBytecode.get? pc.toNat = some byte → parseInstr byte = some instr →
      WindowDisjointFromWrites 3186 (pc.toNat + 1) (argOnNBytesOfInstr instr)
        (runtimeWrites v))
    (harghi : ∀ byte instr,
      attesterBytecode.get? pc.toNat = some byte → parseInstr byte = some instr →
      pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 3186) :
    decode (patchedRuntime v) pc = decode attesterBytecode pc := by
  refine decode_eq_of_get?_arg_eq (patchedRuntime v) attesterBytecode pc
    (patchedRuntime_get?_preserved v pc.toNat hgetwin hgethi) ?_
  intro byte instr hbyte hinstr
  exact patchedRuntime_extract'_preserved_len v (pc.toNat + 1) (argOnNBytesOfInstr instr)
    (hargwin byte instr hbyte hinstr)
    (by have h := harghi byte instr hbyte hinstr; omega)
    (harghi byte instr hbyte hinstr)

theorem patchedRuntime_decode_preserved_of_parse (v : AttesterImmutables) (pc : UInt256)
    (byte : UInt8) (instr : Operation)
    (hbyte : attesterBytecode.get? pc.toNat = some byte)
    (hinstr : parseInstr byte = some instr)
    (hgetwin : WindowDisjointFromWrites 3186 pc.toNat 1 (runtimeWrites v))
    (hgethi : pc.toNat + 1 ≤ 3186)
    (hargwin :
      WindowDisjointFromWrites 3186 (pc.toNat + 1) (argOnNBytesOfInstr instr)
        (runtimeWrites v))
    (harghi : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 3186) :
    decode (patchedRuntime v) pc = decode attesterBytecode pc := by
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

theorem attesterAccountAddress_ofNat_toNat (a : AccountAddress) :
    AccountAddress.ofNat (↑a : Nat) = a := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt a.isLt

theorem attesterEvalAddrLit (cfg : Config) (frame : Frame) (evm : EVM.State)
    (a : AccountAddress) :
    evalExpr? cfg frame evm (addrLit a) = .ok (.address a) := by
  simp only [addrLit, evalExpr?, EvalResult.bind, bind, pure, castValue?]
  rw [if_neg]
  · simp [EvalResult.ofOption, attesterAccountAddress_ofNat_toNat]
  · exact not_lt.mpr (Int.natCast_nonneg (↑a : Nat))

theorem attesterEvalEasExpr (v : AttesterImmutables) (frame : Frame) (evm : EVM.State) :
    evalExpr? (config v) frame evm (easExpr v) = .ok (.address v.eas) := by
  exact attesterEvalAddrLit (config v) frame evm v.eas

/-- Trusted jump-destination fact for the non-payable guard target in the patched runtime. -/
axiom attesterGuardJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨15⟩ : UInt256) = true

/-- Trusted jump-destination fact for the dispatch no-match/short-calldata revert target. -/
axiom attesterDispatchRevertJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨74⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiRevoke(bytes32[],bytes32[][])` wrapper entry. -/
axiom attesterMultiRevokeWrapperJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨78⟩ : UInt256) = true

/-- Trusted jump-destination fact for the post-decode `multiRevoke(bytes32[],bytes32[][])` wrapper block. -/
axiom attesterMultiRevokeDecodedJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨92⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiRevoke(bytes32[],bytes32[][])` function body entry. -/
axiom attesterMultiRevokeBodyJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨192⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiAttest(bytes32[],uint256[][])` wrapper entry. -/
axiom attesterMultiAttestWrapperJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨99⟩ : UInt256) = true

/-- Trusted jump-destination fact for the post-decode `multiAttest(bytes32[],uint256[][])` wrapper block. -/
axiom attesterMultiAttestDecodedJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨113⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiAttest(bytes32[],uint256[][])` function body entry. -/
axiom attesterMultiAttestBodyJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨828⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared two-dynamic-argument ABI decoder. -/
axiom attesterDynamic2DecoderJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2109⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful first length check in the shared dynamic decoder. -/
axiom attesterDynamic2DecodeHeadOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2128⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful first offset check in the shared dynamic decoder. -/
axiom attesterDynamic2FirstOffsetOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2149⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared dynamic-array decoder routine. -/
axiom attesterDynamicArrayDecoderJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2038⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `attest(bytes32,uint256)` wrapper entry. -/
axiom attesterAttestWrapperJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨140⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `attest(bytes32,uint256)` ABI decoder. -/
axiom attesterAttestDecoderJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2281⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful `attest(bytes32,uint256)` decode branch. -/
axiom attesterAttestDecodeOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2298⟩ : UInt256) = true

/-- Trusted jump-destination fact for the post-decode `attest(bytes32,uint256)` wrapper block. -/
axiom attesterAttestDecodedJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨154⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `attest(bytes32,uint256)` function body entry. -/
axiom attesterAttestBodyJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1595⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `attest(bytes32,uint256)` ABI encoder return. -/
axiom attesterAttestEncodeTailJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1737⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `attest(bytes32,uint256)` calldata-encoded block. -/
axiom attesterAttestCallDataEncodedJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1792⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared `AttestationRequest` ABI encoder entry. -/
axiom attesterAttestEncodeRequestJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨3106⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared `AttestationRequestData` tuple encoder entry. -/
axiom attesterAttestEncodeTupleJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2604⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared `AttestationRequestData` tuple encoder return. -/
axiom attesterAttestEncodeTupleReturnJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨3142⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful external `attest` call branch. -/
axiom attesterAttestCallOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1820⟩ : UInt256) = true

/-- Trusted jump-destination fact for the external `attest` return decoder entry. -/
axiom attesterAttestReturnDecodeJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨3150⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful external `attest` return decoder branch. -/
axiom attesterAttestReturnDecodeOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨3166⟩ : UInt256) = true

/-- Trusted jump-destination fact for the post-return-decoder `attest(bytes32,uint256)` body block. -/
axiom attesterAttestAfterReturnDecodeJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1856⟩ : UInt256) = true

/-- Trusted jump-destination fact for the shared public one-word return wrapper. -/
axiom attesterAttestPublicReturnJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨159⟩ : UInt256) = true

/-- Trusted jump-destination fact for the final `RETURN` block of the public wrapper. -/
axiom attesterAttestFinalReturnJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨131⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `revoke(bytes32,bytes32)` wrapper entry. -/
axiom attesterRevokeWrapperJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨173⟩ : UInt256) = true

/-- Trusted jump-destination fact for the post-decode `revoke(bytes32,bytes32)` wrapper block. -/
axiom attesterRevokeDecodedJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨187⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `revoke(bytes32,bytes32)` function body entry. -/
axiom attesterRevokeBodyJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨1863⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful external-code-size check in `revoke`. -/
axiom attesterRevokeExtcodesizeOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2012⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful external `revoke` call branch. -/
axiom attesterRevokeCallOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2030⟩ : UInt256) = true

/-- Trusted jump-destination fact for public wrappers that finish without return data. -/
axiom attesterNoReturnDoneJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨97⟩ : UInt256) = true

theorem writeWord_size_of_inside (mem : ByteArray) (off : Nat) (word : UInt256)
    (hinside : off + 32 ≤ mem.size) :
    (Reasoning.Theory.writeWord mem off word).size = mem.size := by
  have hgap : off - mem.size < USize.size := by
    have hoff : off ≤ mem.size := by omega
    rw [Nat.sub_eq_zero_of_le hoff]
    exact lt_usize 0 (by norm_num)
  rw [writeWord_size mem off word hgap]
  exact max_eq_left hinside

set_option maxHeartbeats 1000000 in
theorem decode_writeWord_below (mem : ByteArray) (off : Nat) (word : UInt256)
    (pc : UInt256)
    (hwin : pc.toNat + 33 ≤ off)
    (hinside : off + 32 ≤ mem.size)
    (hsize : mem.size < 2 ^ 64) :
    decode (Reasoning.Theory.writeWord mem off word) pc = decode mem pc := by
  have hwrite :
      Reasoning.Theory.writeWord mem off word =
        mem.extract 0 off ++ UInt256.toByteArray word ++ mem.extract (off + 32) mem.size := by
    unfold Reasoning.Theory.writeWord
    rw [write32_eq _ _ off (by rw [toByteArray_size]) (by omega)]
    rw [toByteArray_extract_all]
  have hprefixSize : (mem.extract 0 off).size = off := by
    rw [ByteArray.size_extract]
    omega
  have hsplit : mem.extract 0 off ++ mem.extract off mem.size = mem := by
    have h := (ByteArray.extract_append_extract (a := mem) (i := 0) (j := off) (k := mem.size))
    simpa [Nat.min_eq_left (Nat.zero_le off), Nat.max_eq_right (by omega),
      ByteArray.extract_zero_size] using h
  calc
    decode (Reasoning.Theory.writeWord mem off word) pc =
        decode (mem.extract 0 off) pc := by
      rw [hwrite]
      rw [ByteArray.append_assoc]
      exact decode_append_left_window (mem.extract 0 off)
        (UInt256.toByteArray word ++ mem.extract (off + 32) mem.size) pc
        (by rw [hprefixSize]; exact hwin)
        (by rw [hprefixSize]; omega)
    _ = decode (mem.extract 0 off ++ mem.extract off mem.size) pc := by
      symm
      exact decode_append_left_window (mem.extract 0 off) (mem.extract off mem.size) pc
        (by rw [hprefixSize]; exact hwin)
        (by rw [hprefixSize]; omega)
    _ = decode mem pc := by rw [hsplit]

theorem decode_patchedRuntime_eq_attesterBytecode (v : AttesterImmutables)
    (pc : UInt256) (hwin : pc.toNat + 33 ≤ 722) :
    decode (patchedRuntime v) pc = decode attesterBytecode pc := by
  let w : UInt256 := EVM.Word.ofNat v.eas.toNat
  change
    decode (writeCascade attesterBytecode [(722, w), (1465, w), (1598, w), (1939, w)])
      pc = decode attesterBytecode pc
  simp only [writeCascade]
  have hs0 : attesterBytecode.size = 3186 := attesterBytecode_size
  have hs1 : (writeWord attesterBytecode 722 w).size = 3186 := by
    rw [writeWord_size_of_inside attesterBytecode 722 w (by rw [hs0]; norm_num), hs0]
  have hs2 : (writeWord (writeWord attesterBytecode 722 w) 1465 w).size = 3186 := by
    rw [writeWord_size_of_inside (writeWord attesterBytecode 722 w) 1465 w
      (by rw [hs1]; norm_num), hs1]
  have hs3 :
      (writeWord (writeWord (writeWord attesterBytecode 722 w) 1465 w) 1598 w).size =
        3186 := by
    rw [writeWord_size_of_inside
      (writeWord (writeWord attesterBytecode 722 w) 1465 w) 1598 w
      (by rw [hs2]; norm_num), hs2]
  rw [decode_writeWord_below
    (writeWord (writeWord (writeWord attesterBytecode 722 w) 1465 w) 1598 w)
    1939 w pc (by omega) (by rw [hs3]; norm_num) (by rw [hs3]; norm_num)]
  rw [decode_writeWord_below
    (writeWord (writeWord attesterBytecode 722 w) 1465 w)
    1598 w pc (by omega) (by rw [hs2]; norm_num) (by rw [hs2]; norm_num)]
  rw [decode_writeWord_below
    (writeWord attesterBytecode 722 w)
    1465 w pc (by omega) (by rw [hs1]; norm_num) (by rw [hs1]; norm_num)]
  rw [decode_writeWord_below
    attesterBytecode 722 w pc hwin (by rw [hs0]; norm_num) (by rw [hs0]; norm_num)]

theorem uInt256OfByteArray_toByteArray (w : UInt256) :
    uInt256OfByteArray (UInt256.toByteArray w) = w := by
  rw [uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem patchedRuntime_word722 (v : AttesterImmutables) :
    (patchedRuntime v).extract' 722 (722 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 722 32 (by norm_num) (by norm_num)]
  · refine writeCascade_read_word_of_head_of_base attesterBytecode
      (base := 3186) (EVM.Word.ofNat v.eas.toNat)
      [ (1465, EVM.Word.ofNat v.eas.toNat),
        (1598, EVM.Word.ofNat v.eas.toNat),
        (1939, EVM.Word.ofNat v.eas.toNat) ] ?_ ?_ ?_
    · exact attesterBytecode_size
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 722 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word1465 (v : AttesterImmutables) :
    (patchedRuntime v).extract' 1465 (1465 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 1465 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat))
      (base := 3186) (EVM.Word.ofNat v.eas.toNat)
      [ (1598, EVM.Word.ofNat v.eas.toNat),
        (1939, EVM.Word.ofNat v.eas.toNat) ] ?_ ?_ ?_
    · rw [writeWord_size_of_inside attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)
        (by rw [attesterBytecode_size]; norm_num), attesterBytecode_size]
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 1465 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word1598 (v : AttesterImmutables) :
    (patchedRuntime v).extract' 1598 (1598 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 1598 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons, writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
        (EVM.Word.ofNat v.eas.toNat))
      (base := 3186) (EVM.Word.ofNat v.eas.toNat)
      [ (1939, EVM.Word.ofNat v.eas.toNat) ] ?_ ?_ ?_
    · have hs1 :
          (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
        rw [writeWord_size_of_inside attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)
          (by rw [attesterBytecode_size]; norm_num), attesterBytecode_size]
      rw [writeWord_size_of_inside
        (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
        (EVM.Word.ofNat v.eas.toNat) (by rw [hs1]; norm_num), hs1]
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 1598 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem patchedRuntime_word1939 (v : AttesterImmutables) :
    (patchedRuntime v).extract' 1939 (1939 + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.eas.toNat) := by
  unfold patchedRuntime runtimeWrites
  unfold ByteArray.extract'
  rw [if_pos (by native_decide)]
  rw [← readWithPadding_eq_extract' _ 1939 32 (by norm_num) (by norm_num)]
  · rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
    refine writeCascade_read_word_of_head_of_base
      (writeWord
        (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
          (EVM.Word.ofNat v.eas.toNat)) 1598 (EVM.Word.ofNat v.eas.toNat))
      (base := 3186) (EVM.Word.ofNat v.eas.toNat) [] ?_ ?_ ?_
    · have hs1 :
          (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
        rw [writeWord_size_of_inside attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)
          (by rw [attesterBytecode_size]; norm_num), attesterBytecode_size]
      have hs2 :
          (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
            (EVM.Word.ofNat v.eas.toNat)).size = 3186 := by
        rw [writeWord_size_of_inside
          (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
          (EVM.Word.ofNat v.eas.toNat) (by rw [hs1]; norm_num), hs1]
      rw [writeWord_size_of_inside
        (writeWord (writeWord attesterBytecode 722 (EVM.Word.ofNat v.eas.toNat)) 1465
          (EVM.Word.ofNat v.eas.toNat)) 1598 (EVM.Word.ofNat v.eas.toNat)
        (by rw [hs2]; norm_num), hs2]
    · norm_num
    · simp [WindowDisjointFromWrites]
  · change 1939 + 32 ≤ (patchedRuntime v).size
    rw [patchedRuntime_size v]
    norm_num

theorem attesterDecodeEasWord721 (v : AttesterImmutables) :
    decode (patchedRuntime v) ⟨721⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.eas.toNat, 32)) := by
  unfold decode
  rw [show (⟨721⟩ : UInt256).toNat = 721 by native_decide]
  rw [patchedRuntime_get?_preserved v 721]
  · have hget : attesterBytecode.get? 721 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word722 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem attesterDecodeEasWord1464 (v : AttesterImmutables) :
    decode (patchedRuntime v) ⟨1464⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.eas.toNat, 32)) := by
  unfold decode
  rw [show (⟨1464⟩ : UInt256).toNat = 1464 by native_decide]
  rw [patchedRuntime_get?_preserved v 1464]
  · have hget : attesterBytecode.get? 1464 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word1465 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem attesterDecodeEasWord1597 (v : AttesterImmutables) :
    decode (patchedRuntime v) ⟨1597⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.eas.toNat, 32)) := by
  unfold decode
  rw [show (⟨1597⟩ : UInt256).toNat = 1597 by native_decide]
  rw [patchedRuntime_get?_preserved v 1597]
  · have hget : attesterBytecode.get? 1597 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word1598 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

theorem attesterDecodeEasWord1938 (v : AttesterImmutables) :
    decode (patchedRuntime v) ⟨1938⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.eas.toNat, 32)) := by
  unfold decode
  rw [show (⟨1938⟩ : UInt256).toNat = 1938 by native_decide]
  rw [patchedRuntime_get?_preserved v 1938]
  · have hget : attesterBytecode.get? 1938 = some 0x7f := by native_decide
    rw [hget]
    simp [parseInstr, argOnNBytesOfInstr]
    rw [patchedRuntime_word1939 v]
    rw [uInt256OfByteArray_toByteArray]
    rfl
  · simp [runtimeWrites, WindowDisjointFromWrites]
  · norm_num

def attesterSelIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

abbrev attesterDispatchRevertPc : UInt256 := ⟨74⟩

def attesterRuntimeSelBytes : ℕ → ByteArray
  | 0 => attesterMultiRevokeSelBytes
  | 1 => attesterMultiAttestSelBytes
  | 2 => attesterAttestSelBytes
  | _ => attesterRevokeSelBytes

macro "attester_runtime_decide" : tactic =>
  `(tactic|
    (simp only [solcGuardTgtOp, solcGuardTgt, solcGuardTgtWidth, solcGuardJumpiPc,
      solcDispatchBodyPc, solcCalldataRevertPushPc, solcCalldataRevertTgtOp,
      solcCalldataRevertTgt, solcCalldataRevertTgtWidth, solcCalldataJumpiPc,
      solcSelectorLoadPc, solcFirstArmPcFromPrefix, pushAt, nthArmPc, armSelNat,
      armTgtOp, armTgt, armTgtWidth, selArmPush4Pc, selArmEqPc, selArmPushTgtPc,
      selArmJumpiPc, selArmNextPc, attesterFirstArmPc, attesterDispatchRevertPc];
     repeat
       (rw [decode_patchedRuntime_eq_attesterBytecode _ _ (by native_decide)];
        simp only [solcGuardTgtOp, solcGuardTgt, solcGuardTgtWidth, solcGuardJumpiPc,
          solcDispatchBodyPc, solcCalldataRevertPushPc, solcCalldataRevertTgtOp,
          solcCalldataRevertTgt, solcCalldataRevertTgtWidth, solcCalldataJumpiPc,
          solcSelectorLoadPc, solcFirstArmPcFromPrefix, pushAt, nthArmPc, armSelNat,
          armTgtOp, armTgt, armTgtWidth, selArmPush4Pc, selArmEqPc, selArmPushTgtPc,
          selArmJumpiPc, selArmNextPc, attesterFirstArmPc, attesterDispatchRevertPc]);
     native_decide +revert))

macro "attester_decode" : tactic =>
  `(tactic|
    (first
      | rw [decode_patchedRuntime_eq_attesterBytecode _ _ (by native_decide)]
        native_decide
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

syntax "attester_decode_at " term "," term "," term "," term : tactic
macro_rules
  | `(tactic| attester_decode_at $varg, $pc, $byte, $instr) =>
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

theorem attesterMultiRevokeSelBytes_size : attesterMultiRevokeSelBytes.size = 4 := rfl
theorem attesterMultiAttestSelBytes_size : attesterMultiAttestSelBytes.size = 4 := rfl
theorem attesterAttestSelBytes_size : attesterAttestSelBytes.size = 4 := rfl
theorem attesterRevokeSelBytes_size : attesterRevokeSelBytes.size = 4 := rfl

theorem attesterDispatch_none_short (v : AttesterImmutables) {cd : ByteArray}
    (hcd : cd.size < 4) :
    dispatchMsg (contract v) cd = none := by
  rw [dispatchMsg_eq_dispatchList (contract v) cd (by rfl) (by rfl)]
  exact dispatchList_none_short (contract v).transitions
    (by
      intro t ht
      simp [contract, transitions] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · rw [attestSelectorOf v]; exact attesterAttestSelBytes_size
      · rw [multiAttestSelectorOf v]; exact attesterMultiAttestSelBytes_size
      · rw [multiRevokeSelectorOf v]; exact attesterMultiRevokeSelBytes_size
      · rw [revokeSelectorOf v]; exact attesterRevokeSelBytes_size)
    hcd

theorem attesterDispatch_none_nomatch (v : AttesterImmutables) {cd : ByteArray}
    (hmultiRevoke : (attesterMultiRevokeSelBytes == cd.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == cd.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == cd.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == cd.extract 0 4) = false) :
    dispatchMsg (contract v) cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl) (hreceive := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [attestSelectorOf v]; exact hattest
  · rw [multiAttestSelectorOf v]; exact hmultiAttest
  · rw [multiRevokeSelectorOf v]; exact hmultiRevoke
  · rw [revokeSelectorOf v]; exact hrevoke

theorem attesterSelectorMismatchOfHit {miss hit x : ByteArray}
    (hne : miss ≠ hit) (hhit : (hit == x) = true) :
    (miss == x) = false := by
  by_cases hmiss : (miss == x) = true
  · have hmissEq : miss = x := byteArray_eq_of_beq hmiss
    have hhitEq : hit = x := byteArray_eq_of_beq hhit
    exact False.elim (hne (hmissEq.trans hhitEq.symm))
  · exact Bool.eq_false_of_not_eq_true hmiss

theorem attesterAttestSelBytes_ne_multiAttestSelBytes :
    attesterAttestSelBytes ≠ attesterMultiAttestSelBytes := by
  native_decide

theorem attesterAttestSelBytes_ne_multiRevokeSelBytes :
    attesterAttestSelBytes ≠ attesterMultiRevokeSelBytes := by
  native_decide

theorem attesterMultiAttestSelBytes_ne_multiRevokeSelBytes :
    attesterMultiAttestSelBytes ≠ attesterMultiRevokeSelBytes := by
  native_decide

theorem attesterDispatch_attest (v : AttesterImmutables) {cd : ByteArray}
    (hattest : (attesterAttestSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (attestTransition v) := by
  apply dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := []) (post := [multiAttestTransition v, multiRevokeTransition v, revokeTransition v])
    (ti := attestTransition v) (cd := cd) (hfallback := by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
  · rw [attestSelectorOf v]
    exact hattest

theorem attesterDispatch_multiAttest (v : AttesterImmutables) {cd : ByteArray}
    (hmultiAttest : (attesterMultiAttestSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (multiAttestTransition v) := by
  apply dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [attestTransition v]) (post := [multiRevokeTransition v, revokeTransition v])
    (ti := multiAttestTransition v) (cd := cd) (hfallback := by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl
    rw [attestSelectorOf v]
    exact attesterSelectorMismatchOfHit attesterAttestSelBytes_ne_multiAttestSelBytes hmultiAttest
  · rw [multiAttestSelectorOf v]
    exact hmultiAttest

theorem attesterDispatch_multiRevoke (v : AttesterImmutables) {cd : ByteArray}
    (hmultiRevoke : (attesterMultiRevokeSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (multiRevokeTransition v) := by
  apply dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [attestTransition v, multiAttestTransition v]) (post := [revokeTransition v])
    (ti := multiRevokeTransition v) (cd := cd) (hfallback := by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl
    · rw [attestSelectorOf v]
      exact attesterSelectorMismatchOfHit attesterAttestSelBytes_ne_multiRevokeSelBytes hmultiRevoke
    · rw [multiAttestSelectorOf v]
      exact attesterSelectorMismatchOfHit attesterMultiAttestSelBytes_ne_multiRevokeSelBytes
        hmultiRevoke
  · rw [multiRevokeSelectorOf v]
    exact hmultiRevoke

theorem attesterDispatch_revoke (v : AttesterImmutables) {cd : ByteArray}
    (hmultiRevoke : (attesterMultiRevokeSelBytes == cd.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == cd.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == cd.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some (revokeTransition v) := by
  apply dispatchMsg_eq_some_of_split (contract := contract v)
    (pre := [attestTransition v, multiAttestTransition v, multiRevokeTransition v]) (post := [])
    (ti := revokeTransition v) (cd := cd) (hfallback := by rfl)
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl
    · rw [attestSelectorOf v]
      exact hattest
    · rw [multiAttestSelectorOf v]
      exact hmultiAttest
    · rw [multiRevokeSelectorOf v]
      exact hmultiRevoke
  · rw [revokeSelectorOf v]
    exact hrevoke

theorem attesterMultiRevokeEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false) :
    UInt256.eq (⟨0x13fde550⟩ : UInt256) (solcSelectorWord I) = ⟨0⟩ := by
  simpa [solcSelectorWord, attesterMultiRevokeSelBytes, hmultiRevoke] using
    (evmSelectorDecode (cd := I.calldata) hsz
      (0x13 : UInt8) (0xfd : UInt8) (0xe5 : UInt8) (0x50 : UInt8)
      (⟨0x13fde550⟩ : UInt256) (by native_decide))

theorem attesterMultiRevokeEqNonzero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    UInt256.eq (⟨0x13fde550⟩ : UInt256) (solcSelectorWord I) ≠ ⟨0⟩ := by
  have h :
      UInt256.eq (⟨0x13fde550⟩ : UInt256) (solcSelectorWord I) = ⟨1⟩ := by
    simpa [solcSelectorWord, attesterMultiRevokeSelBytes, hmultiRevoke] using
      (evmSelectorDecode (cd := I.calldata) hsz
        (0x13 : UInt8) (0xfd : UInt8) (0xe5 : UInt8) (0x50 : UInt8)
        (⟨0x13fde550⟩ : UInt256) (by native_decide))
  rw [h]
  decide

theorem attesterMultiAttestEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false) :
    UInt256.eq (⟨0x54e1db35⟩ : UInt256) (solcSelectorWord I) = ⟨0⟩ := by
  simpa [solcSelectorWord, attesterMultiAttestSelBytes, hmultiAttest] using
    (evmSelectorDecode (cd := I.calldata) hsz
      (0x54 : UInt8) (0xe1 : UInt8) (0xdb : UInt8) (0x35 : UInt8)
      (⟨0x54e1db35⟩ : UInt256) (by native_decide))

theorem attesterMultiAttestEqNonzero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    UInt256.eq (⟨0x54e1db35⟩ : UInt256) (solcSelectorWord I) ≠ ⟨0⟩ := by
  have h :
      UInt256.eq (⟨0x54e1db35⟩ : UInt256) (solcSelectorWord I) = ⟨1⟩ := by
    simpa [solcSelectorWord, attesterMultiAttestSelBytes, hmultiAttest] using
      (evmSelectorDecode (cd := I.calldata) hsz
        (0x54 : UInt8) (0xe1 : UInt8) (0xdb : UInt8) (0x35 : UInt8)
        (⟨0x54e1db35⟩ : UInt256) (by native_decide))
  rw [h]
  decide

theorem attesterAttestEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false) :
    UInt256.eq (⟨0x72b9966d⟩ : UInt256) (solcSelectorWord I) = ⟨0⟩ := by
  simpa [solcSelectorWord, attesterAttestSelBytes, hattest] using
    (evmSelectorDecode (cd := I.calldata) hsz
      (0x72 : UInt8) (0xb9 : UInt8) (0x96 : UInt8) (0x6d : UInt8)
      (⟨0x72b9966d⟩ : UInt256) (by native_decide))

theorem attesterAttestEqNonzero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    UInt256.eq (⟨0x72b9966d⟩ : UInt256) (solcSelectorWord I) ≠ ⟨0⟩ := by
  have h :
      UInt256.eq (⟨0x72b9966d⟩ : UInt256) (solcSelectorWord I) = ⟨1⟩ := by
    simpa [solcSelectorWord, attesterAttestSelBytes, hattest] using
      (evmSelectorDecode (cd := I.calldata) hsz
        (0x72 : UInt8) (0xb9 : UInt8) (0x96 : UInt8) (0x6d : UInt8)
        (⟨0x72b9966d⟩ : UInt256) (by native_decide))
  rw [h]
  decide

theorem attesterRevokeEqZero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = false) :
    UInt256.eq (⟨0xc2664610⟩ : UInt256) (solcSelectorWord I) = ⟨0⟩ := by
  simpa [solcSelectorWord, attesterRevokeSelBytes, hrevoke] using
    (evmSelectorDecode (cd := I.calldata) hsz
      (0xc2 : UInt8) (0x66 : UInt8) (0x46 : UInt8) (0x10 : UInt8)
      (⟨0xc2664610⟩ : UInt256) (by native_decide))

theorem attesterRevokeEqNonzero (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    UInt256.eq (⟨0xc2664610⟩ : UInt256) (solcSelectorWord I) ≠ ⟨0⟩ := by
  have h :
      UInt256.eq (⟨0xc2664610⟩ : UInt256) (solcSelectorWord I) = ⟨1⟩ := by
    simpa [solcSelectorWord, attesterRevokeSelBytes, hrevoke] using
      (evmSelectorDecode (cd := I.calldata) hsz
        (0xc2 : UInt8) (0x66 : UInt8) (0x46 : UInt8) (0x10 : UInt8)
        (⟨0xc2664610⟩ : UInt256) (by native_decide))
  rw [h]
  decide

theorem attesterX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  have h12 := h0
    |>.push2 (⟨15⟩ : UInt256) (by attester_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.jumpiNT (by attester_decode) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact h12.push0 (by attester_decode) (by simp)
    |>.dup1 (by attester_decode) (by simp)
    |>.rev 0 (by attester_decode) (fun s _ hstks => memExpRevert0 s hstks) (by simp)

theorem attesterX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 4) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  have h74 := h17
    |>.push1 ⟨4⟩ (by attester_decode) (by simp)
    |>.calldatasize (by attester_decode) (by simp)
    |>.lt (by attester_decode) (by simp)
    |>.push2 attesterDispatchRevertPc (by attester_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)
    |>.jumpiT (by attester_decode) (lt_four_ne_zero_of_lt hshort)
      (attesterDispatchRevertJumpdest v) (by simp only [List.length_nil]; omega)
    |>.jumpdest (by attester_decode) (by simp)
  exact h74.push0 (by attester_decode) (by simp)
    |>.dup1 (by attester_decode) (by simp)
    |>.rev 0 (by attester_decode) (fun s _ hstks => memExpRevert0 s hstks) (by simp)

theorem attesterX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = false) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  obtain ⟨k25, C25, h25raw⟩ := solcCalldataOk
    (bodyPc := (⟨17⟩ : UInt256)) (selLoadTgt := attesterDispatchRevertPc)
    (opR := .PUSH2) (wR := 2)
    h17 hsz hsize (by attester_decode) (by attester_decode) (by attester_decode)
    (by decide) (by attester_decode) (by attester_decode)
  have h25 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨25⟩ : UInt256)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k25 C25 := by
    simpa using h25raw
  obtain ⟨k30, C30, h30raw⟩ := solcSelectorLoad h25
    (by attester_decode) (by attester_decode) (by attester_decode) (by attester_decode) (by simp)
  have h30 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) attesterFirstArmPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k30 C30 := by
    simpa [attesterFirstArmPc, solcSelectorWord] using h30raw
  have heqMultiRevoke := attesterMultiRevokeEqZero I hsz hmultiRevoke
  have heqMultiAttest := attesterMultiAttestEqZero I hsz hmultiAttest
  have heqAttest := attesterAttestEqZero I hsz hattest
  have heqRevoke := attesterRevokeEqZero I hsz hrevoke
  have h74 := h30
    |>.selectorArmNotTaken (selNat := (⟨0x13fde550⟩ : UInt256))
      (tgt := (⟨78⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiRevoke (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0x54e1db35⟩ : UInt256))
      (tgt := (⟨99⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiAttest (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0x72b9966d⟩ : UInt256))
      (tgt := (⟨140⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqAttest (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0xc2664610⟩ : UInt256))
      (tgt := (⟨173⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqRevoke (by simp)
    |>.jumpdest (by attester_decode) (by simp)
  exact h74.push0 (by attester_decode) (by simp)
    |>.dup1 (by attester_decode) (by simp)
    |>.rev 0 (by attester_decode) (fun s _ hstks => memExpRevert0 s hstks) (by simp)

theorem attesterX_multiRevokeWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨78⟩ : UInt256)
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  obtain ⟨k25, C25, h25raw⟩ := solcCalldataOk
    (bodyPc := (⟨17⟩ : UInt256)) (selLoadTgt := attesterDispatchRevertPc)
    (opR := .PUSH2) (wR := 2)
    h17 hsz hsize (by attester_decode) (by attester_decode) (by attester_decode)
    (by decide) (by attester_decode) (by attester_decode)
  have h25 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨25⟩ : UInt256)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k25 C25 := by
    simpa using h25raw
  obtain ⟨k30, C30, h30raw⟩ := solcSelectorLoad h25
    (by attester_decode) (by attester_decode) (by attester_decode) (by attester_decode) (by simp)
  have h30 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) attesterFirstArmPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k30 C30 := by
    simpa [attesterFirstArmPc, solcSelectorWord] using h30raw
  have heqMultiRevoke := attesterMultiRevokeEqNonzero I hsz hmultiRevoke
  exact ⟨_, _, h30
    |>.selectorArmTaken (selNat := (⟨0x13fde550⟩ : UInt256))
      (tgt := (⟨78⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiRevoke
      (attesterMultiRevokeWrapperJumpdest v) (by simp)⟩

theorem attesterX_multiAttestWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨99⟩ : UInt256)
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  obtain ⟨k25, C25, h25raw⟩ := solcCalldataOk
    (bodyPc := (⟨17⟩ : UInt256)) (selLoadTgt := attesterDispatchRevertPc)
    (opR := .PUSH2) (wR := 2)
    h17 hsz hsize (by attester_decode) (by attester_decode) (by attester_decode)
    (by decide) (by attester_decode) (by attester_decode)
  have h25 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨25⟩ : UInt256)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k25 C25 := by
    simpa using h25raw
  obtain ⟨k30, C30, h30raw⟩ := solcSelectorLoad h25
    (by attester_decode) (by attester_decode) (by attester_decode) (by attester_decode) (by simp)
  have h30 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) attesterFirstArmPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k30 C30 := by
    simpa [attesterFirstArmPc, solcSelectorWord] using h30raw
  have heqMultiRevoke := attesterMultiRevokeEqZero I hsz hmultiRevoke
  have heqMultiAttest := attesterMultiAttestEqNonzero I hsz hmultiAttest
  exact ⟨_, _, h30
    |>.selectorArmNotTaken (selNat := (⟨0x13fde550⟩ : UInt256))
      (tgt := (⟨78⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiRevoke (by simp)
    |>.selectorArmTaken (selNat := (⟨0x54e1db35⟩ : UInt256))
      (tgt := (⟨99⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiAttest
      (attesterMultiAttestWrapperJumpdest v) (by simp)⟩

theorem attesterX_multiRevokeToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨78⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2109⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨92⟩, ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd78⟩ := hreach
  exact ⟨_, _, evm_run rd78 with [
    raw jumpdest (by attester_decode_at v, ⟨78⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨97⟩ (by attester_decode_at v, ⟨79⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw push2 ⟨92⟩ (by attester_decode_at v, ⟨82⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨85⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨86⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push2 ⟨2109⟩ (by attester_decode_at v, ⟨88⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨91⟩, 0x56, .JUMP)
      (attesterDynamic2DecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨99⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2109⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨113⟩, ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd99⟩ := hreach
  exact ⟨_, _, evm_run rd99 with [
    raw jumpdest (by attester_decode_at v, ⟨99⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨118⟩ (by attester_decode_at v, ⟨100⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw push2 ⟨113⟩ (by attester_decode_at v, ⟨103⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨106⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨107⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push2 ⟨2109⟩ (by attester_decode_at v, ⟨109⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨112⟩, 0x56, .JUMP)
      (attesterDynamic2DecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2DecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2109⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2109⟩ := hreach
  exact evm_run rd2109 with [
    raw jumpdest (by attester_decode_at v, ⟨2109⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2110⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2111⟩, 0x80, .DUP1) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2112⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2113⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2114⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2116⟩, 0x85, .DUP6) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2117⟩, 0x87, .DUP8) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2118⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2119⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2120⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2128⟩ (by attester_decode_at v, ⟨2121⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2124⟩, 0x57, .JUMPI) (by rw [hslt]; decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2125⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2126⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2127⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamic2DecodeHeadOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2109⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2128⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2109⟩ := hreach
  exact ⟨_, _, evm_run rd2109 with [
    raw jumpdest (by attester_decode_at v, ⟨2109⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2110⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2111⟩, 0x80, .DUP1) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2112⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2113⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2114⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2116⟩, 0x85, .DUP6) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2117⟩, 0x87, .DUP8) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2118⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2119⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2120⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2128⟩ (by attester_decode_at v, ⟨2121⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2124⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (attesterDynamic2DecodeHeadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2FirstOffsetOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2128⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2149⟩ : UInt256)
      [calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2128⟩ := hreach
  have hgt :
      UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hmaxToNat]
    exact Nat.le_of_not_gt hoffMax
  exact ⟨_, _, evm_run rd2128 with [
    raw jumpdest (by attester_decode_at v, ⟨2128⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2129⟩, 0x84, .DUP5) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2130⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2131⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2133⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2135⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2137⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2138⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2139⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2140⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2141⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2149⟩ (by attester_decode_at v, ⟨2142⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2145⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (calldataWord I.calldata 4)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterDynamic2FirstOffsetOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2FirstOffsetHugeReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoff : solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2128⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2128⟩ := hreach
  have hgt :
      UInt256.gt (calldataWord I.calldata 4)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hmaxToNat]
    exact hoff
  exact evm_run rd2128 with [
    raw jumpdest (by attester_decode_at v, ⟨2128⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2129⟩, 0x84, .DUP5) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2130⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2131⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2133⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2135⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2137⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2138⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2139⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2140⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2141⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2149⟩ (by attester_decode_at v, ⟨2142⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2145⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (calldataWord I.calldata 4)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩
        rw [hgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2146⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2147⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2148⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamic2FirstArrayDecoderEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2149⟩ : UInt256)
      [calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ⟨2161⟩, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2149⟩ := hreach
  exact ⟨_, _, evm_run rd2149 with [
    raw jumpdest (by attester_decode_at v, ⟨2149⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨2161⟩ (by attester_decode_at v, ⟨2150⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2153⟩, 0x87, .DUP8) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2154⟩, 0x82, .DUP3) (by evm_ov),
    raw dup9 (by attester_decode_at v, ⟨2155⟩, 0x88, .DUP9) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2156⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨2038⟩ (by attester_decode_at v, ⟨2157⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2160⟩, 0x56, .JUMP)
      (attesterDynamicArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact attesterX_dynamic2DecodeRevert (v := v) hslt
    (attesterX_multiRevokeToDecoder (v := v)
      (attesterX_multiRevokeWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke))

theorem attesterX_multiRevokeDecodeHeadOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨2128⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨92⟩, ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  exact attesterX_dynamic2DecodeHeadOk (v := v) hslt
    (attesterX_multiRevokeToDecoder (v := v)
      (attesterX_multiRevokeWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke))

theorem attesterX_multiRevokeDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact attesterX_dynamic2DecodeRevert (v := v) hslt
    (attesterX_multiRevokeToDecoder (v := v)
      (attesterX_multiRevokeWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke))

theorem attesterX_multiAttestDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact attesterX_dynamic2DecodeRevert (v := v) hslt
    (attesterX_multiAttestToDecoder (v := v)
      (attesterX_multiAttestWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke
        hmultiAttest))

theorem attesterX_multiAttestDecodeHeadOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨2128⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨113⟩, ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  exact attesterX_dynamic2DecodeHeadOk (v := v) hslt
    (attesterX_multiAttestToDecoder (v := v)
      (attesterX_multiAttestWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke
        hmultiAttest))

theorem attesterX_multiAttestDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact attesterX_dynamic2DecodeRevert (v := v) hslt
    (attesterX_multiAttestToDecoder (v := v)
      (attesterX_multiAttestWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke
        hmultiAttest))

private theorem decodeABIValues_twoDynamicArrays_shape {elem0 elem1 : ABIType}
    {bytes : List UInt8} {values : List Value} {endOffset : Nat}
    (hvals :
      decodeABIValues? [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
        bytes 0 0 64 64 = some (values, endOffset)) :
    ∃ xs ys : List Value, values = [.array xs, .array ys] := by
  rw [decodeABIValues?] at hvals
  simp [isDynamicABIType, bind, Option.bind] at hvals
  cases hread0 : readNat? bytes 0 with
  | none => simp [hread0] at hvals
  | some off0 =>
      by_cases hmax0 : solcMaxLen DecodeMode.modern < off0
      · simp [hread0] at hvals
        have hle : off0 ≤ solcMaxU64 := hvals.1
        simp [solcMaxLen] at hmax0
        omega
      · simp [hread0] at hvals
        cases hv0 : decodeABIValue? (.dynamicArray elem0) bytes off0 with
        | none => simp [hv0] at hvals
        | some p0 =>
            rcases p0 with ⟨v0, end0⟩
            obtain ⟨xs, hv0arr⟩ := decodeABIValue_dynamicArray_is_array hv0
            simp [hv0] at hvals
            cases hrest :
                decodeABIValues? [.dynamicArray (.dynamicArray elem1)]
                  bytes 0 32 64 (max 64 end0) with
            | none => simp [hrest] at hvals
            | some prest =>
                rcases prest with ⟨valuesRest, endRest⟩
                simp [hrest] at hvals
                rw [decodeABIValues?] at hrest
                simp [isDynamicABIType, bind, Option.bind] at hrest
                cases hread1 : readNat? bytes 32 with
                | none => simp [hread1] at hrest
                | some off1 =>
                    by_cases hmax1 : solcMaxLen DecodeMode.modern < off1
                    · simp [hread1] at hrest
                      have hle : off1 ≤ solcMaxU64 := hrest.1
                      simp [solcMaxLen] at hmax1
                      omega
                    · simp [hread1] at hrest
                      cases hv1 :
                          decodeABIValue? (.dynamicArray (.dynamicArray elem1)) bytes off1 with
                      | none => simp [hv1] at hrest
                      | some p1 =>
                          rcases p1 with ⟨v1, end1⟩
                          obtain ⟨ys, hv1arr⟩ := decodeABIValue_dynamicArray_is_array hv1
                          simp [hv1] at hrest
                          rcases hrest with ⟨_hoff1le, hrestEq⟩
                          simp [decodeABIValues?] at hrestEq
                          rcases hrestEq with ⟨hvaluesRestEq, _hendRestEq⟩
                          rcases hvals with ⟨_hoff0le, hvalsEq⟩
                          rcases hvalsEq with ⟨hvaluesEq, _hendEq⟩
                          cases hvaluesRestEq
                          refine ⟨xs, ys, ?_⟩
                          rw [← hvaluesEq, hv0arr, hv1arr]

theorem attesterDecodeCalldata_twoDynamicArrays_none_firstOffsetHuge {cd : ByteArray}
    {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoff : solcMaxU64 < (calldataWord cd 4).toNat) :
    decodeCalldata [name0, name1] [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray elem0, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray elem0, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      have hread := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      simp [decodeCalldata.decodeArgs, decodeABIValues?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, hread, hoff]

theorem attesterDecodeCalldata_twoDynamicArrays_firstOffsetMax {cd : ByteArray}
    {callargs : Store} {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hdec : decodeCalldata [name0, name1] [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
        cd = some callargs) :
    ¬ solcMaxU64 < (calldataWord cd 4).toNat := by
  unfold decodeCalldata at hdec
  simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType,
    bind, Option.bind] at hdec
  rcases hdec with ⟨_hlen4, _hhuge, _hargHuge, _htotalHuge, hdec⟩
  by_cases hshort : cd.toList.length - 4 < 64
  · simp [hshort] at hdec
  · simp [hshort] at hdec
    cases hvals :
        decodeABIValues? [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
          (List.drop 4 cd.toList) 0 0 64 64 with
    | none =>
        simp [hvals] at hdec
    | some p =>
        simp [hvals] at hdec
        rw [decodeABIValues?] at hvals
        simp [isDynamicABIType, bind, Option.bind] at hvals
        cases hread0 : readNat? (List.drop 4 cd.toList) 0 with
        | none => simp [hread0] at hvals
        | some off0 =>
            by_cases hmax0 : solcMaxLen DecodeMode.modern < off0
            · simp [hread0] at hvals
              have hle : off0 ≤ solcMaxU64 := hvals.1
              simp [solcMaxLen] at hmax0
              omega
            · have hreadWord := readNat_drop4_zero_eq_calldataWord (cd := cd)
                (by omega : 36 ≤ cd.size)
              rw [hread0] at hreadWord
              cases hreadWord
              simpa [solcMaxLen] using hmax0

theorem attesterDecodeCalldata_twoDynamicArrays_shape {cd : ByteArray} {callargs : Store}
    {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hne : (name1 == name0) = false)
    (hdec : decodeCalldata [name0, name1] [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
        cd = some callargs) :
    ∃ xs ys : List Value,
      callargs.get? name0 = some (.array xs) ∧
      callargs.get? name1 = some (.array ys) := by
  unfold decodeCalldata at hdec
  simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType,
    bind, Option.bind] at hdec
  rcases hdec with ⟨_hlen4, _hhuge, _hargHuge, _htotalHuge, hdec⟩
  by_cases hshort : cd.toList.length - 4 < 64
  · simp [hshort] at hdec
  · simp [hshort] at hdec
    cases hvals :
        decodeABIValues? [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
          (List.drop 4 cd.toList) 0 0 64 64 with
    | none =>
        simp [hvals] at hdec
    | some p =>
        rcases p with ⟨values, endOffset⟩
        simp [hvals] at hdec
        obtain ⟨xs, ys, hshape⟩ := decodeABIValues_twoDynamicArrays_shape hvals
        cases hshape
        simp [decodeCalldata.insertValues] at hdec
        cases hdec
        refine ⟨xs, ys, ?_, ?_⟩
        · simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert, hne]
        · simp [Std.HashMap.get?_eq_getElem?]

private theorem evalAnd_false_left {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr}
    (hleft : evalExpr? cfg solm evm lhs = .ok (.bool false)) :
    evalExpr? cfg solm evm (.binary .and lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, hleft, EvalResult.bind, bind, pure]

private theorem evalAnd_true_right_false {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr}
    (hleft : evalExpr? cfg solm evm lhs = .ok (.bool true))
    (hright : evalExpr? cfg solm evm rhs = .ok (.bool false)) :
    evalExpr? cfg solm evm (.binary .and lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, hleft, hright, EvalResult.bind, bind, pure]

private theorem evalBinaryEq_of {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {v₁ v₂ value : Value}
    (hleft : evalExpr? cfg solm evm lhs = .ok v₁)
    (hright : evalExpr? cfg solm evm rhs = .ok v₂)
    (hop : evalBinaryOp? .eq v₁ v₂ = .ok value) :
    evalExpr? cfg solm evm (.binary .eq lhs rhs) = .ok value := by
  simp [evalExpr?, hleft, hright, hop, EvalResult.bind, bind]

theorem attesterEvalMultiLengthGuardFalse (v : AttesterImmutables)
    (evm : EVM.State) (locals : Store) {secondName : Ident}
    {schemas second : List Value}
    (hSecond :
      (locals.insert "schemaLength" (.int (Int.ofNat schemas.length)))[secondName]? =
        some (.array second))
    (hbad : schemas.length = 0 ∨ schemas.length ≠ second.length) :
    evalExpr? (config v)
      { contract := contract v,
        locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
      (.binary .and
        (.binary .ne (.var "schemaLength") (.intLit 0))
        (.binary .eq (.var "schemaLength") (lenLocal secondName))) =
      .ok (.bool false) := by
  rcases hbad with hzero | hne
  · have hleft :
        evalExpr? (config v)
          { contract := contract v,
            locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
          (.binary .ne (.var "schemaLength") (.intLit 0)) =
        .ok (.bool false) := by
      simp [evalExpr?, evalBinaryOp?, hzero,
        EvalResult.bind, EvalResult.ofOption, bind, pure]
    exact evalAnd_false_left hleft
  · by_cases hzero : schemas.length = 0
    · have hleft :
          evalExpr? (config v)
            { contract := contract v,
              locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
            (.binary .ne (.var "schemaLength") (.intLit 0)) =
          .ok (.bool false) := by
        simp [evalExpr?, evalBinaryOp?, hzero,
          EvalResult.bind, EvalResult.ofOption, bind, pure]
      exact evalAnd_false_left hleft
    · have hleft :
          evalExpr? (config v)
            { contract := contract v,
              locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
            (.binary .ne (.var "schemaLength") (.intLit 0)) =
          .ok (.bool true) := by
        simp [evalExpr?, evalBinaryOp?, hzero,
          EvalResult.bind, EvalResult.ofOption, bind, pure]
      have hright :
          evalExpr? (config v)
            { contract := contract v,
              locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
            (.binary .eq (.var "schemaLength") (lenLocal secondName)) =
          .ok (.bool false) := by
        have hvar :
            evalExpr? (config v)
              { contract := contract v,
                locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
              (.var "schemaLength") =
            .ok (.int (Int.ofNat schemas.length)) := by
          simp [evalExpr?, EvalResult.ofOption]
        have hlen :
            evalExpr? (config v)
              { contract := contract v,
                locals := locals.insert "schemaLength" (.int (Int.ofNat schemas.length)) } evm
              (lenLocal secondName) =
            .ok (.int (Int.ofNat second.length)) := by
          simp [evalExpr?, lenLocal, localRef, readLocalPath?,
            EvalResult.bind, bind, pure]
          have hSecond' :
              (Std.HashMap.insert locals "schemaLength" (Value.int ↑schemas.length))[secondName]? =
                some (.array second) := by
            simpa using hSecond
          rw [hSecond']
        have hop :
            evalBinaryOp? .eq (.int (Int.ofNat schemas.length))
              (.int (Int.ofNat second.length)) = .ok (.bool false) := by
          simpa [evalBinaryOp?] using hne
        exact evalBinaryEq_of hvar hlen hop
      exact evalAnd_true_right_false hleft hright

theorem attesterBodyReverts_nonPayable (v : AttesterImmutables) (t : TransitionDecl)
    (ht : t ∈ (contract v).transitions) (evm : EVM.State) (callargs : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm callargs t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact bodyReverts_nonPayable hwv

/-- `callvalue != 0` reverts in the shared non-payable guard before ABI dispatch. -/
theorem attesterNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  exact (attesterX_callvalue_ne (g := Sat256.ofUInt256 g) v hIcode hwv).reEquivElim hIcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg (contract v) I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ (contract v).transitions := by
          rw [dispatchMsg_eq_dispatchList (contract v) I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode (config v).abiDecodeMode
            (t.params.map Param.name) (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (attesterBodyReverts_nonPayable v t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- Calldata shorter than the 4-byte selector falls through to the shared revert path. -/
theorem attesterNoDispatchShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hshort : I.calldata.size < 4)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  exact (attesterX_short (g := Sat256.ofUInt256 g) v hIcode hwv hshort)
    |>.reEquivNoDispatch hIcode (attesterDispatch_none_short v hshort)

/-- No public Attester selector matched, so the dispatcher reaches the shared revert path. -/
theorem attesterNoDispatchNoMatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  exact (attesterX_noMatch (g := Sat256.ofUInt256 g) v hIcode hwv hsz4 hsize
      hmultiRevoke hmultiAttest hattest hrevoke)
    |>.reEquivNoDispatch hIcode
      (attesterDispatch_none_nomatch v hmultiRevoke hmultiAttest hattest hrevoke)

end Benchmarks.EAS.Attester
