import Benchmarks.Dss.End.Pack
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `free(bytes32)` transition -/

attribute [local simp]
  endWardsSelectorBytes
  endVatSelectorBytes
  endCatSelectorBytes
  endDogSelectorBytes
  endVowSelectorBytes
  endPotSelectorBytes
  endSpotSelectorBytes
  endCureSelectorBytes
  endLiveSelectorBytes
  endWhenSelectorBytes
  endWaitSelectorBytes
  endDebtSelectorBytes
  endTagSelectorBytes
  endGapSelectorBytes
  endArtSelectorBytes
  endFixSelectorBytes
  endBagSelectorBytes
  endOutSelectorBytes
  endRelySelectorBytes
  endDenySelectorBytes
  endFileAddressSelectorBytes
  endFileUintSelectorBytes
  endCageSelectorBytes
  endCageIlkSelectorBytes
  endSnipSelectorBytes
  endSkipSelectorBytes
  endSkimSelectorBytes
  endFreeSelectorBytes
  endThawSelectorBytes
  endFlowSelectorBytes
  endPackSelectorBytes
  endCashSelectorBytes

abbrev endFreeConcreteSelector : ByteArray := selectorBytes 0xc8 0x30 0x62 0xc6
abbrev endFreeIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I
abbrev endFreeIlkValue (I : ExecutionEnv) : Value :=
  endBytes32ArgValue I
abbrev endFreeStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endFreeIlkValue I)

abbrev endFreeEntryPc : UInt256 := ⟨1025⟩
abbrev endFreeReturnPc : UInt256 := ⟨562⟩
abbrev endFreeDecodedPc : UInt256 := ⟨1047⟩
abbrev endFreeBodyPc : UInt256 := ⟨7690⟩

abbrev endFreeUrnsSelectorWord : UInt256 := ⟨0x2424be5c⟩
abbrev endFreeUrnsSelectorShifted : UInt256 :=
  ⟨0x2424be5c00000000000000000000000000000000000000000000000000000000⟩
abbrev endFreeUrnsOutPtr : UInt256 := ⟨128⟩
abbrev endFreeUrnsInSize : UInt256 := ⟨68⟩
abbrev endFreeUrnsOutSize : UInt256 := ⟨64⟩
abbrev endFreeUrnsEndPtr : UInt256 := ⟨196⟩
abbrev endFreeInt256LimitWord : UInt256 := UInt256.shiftLeft ⟨1⟩ ⟨255⟩

abbrev endFreeGrabSelectorWord : UInt256 := ⟨0x7bab3f40⟩
abbrev endFreeGrabSelectorShifted : UInt256 :=
  ⟨0x7bab3f4000000000000000000000000000000000000000000000000000000000⟩
abbrev endFreeGrabOutPtr : UInt256 := ⟨128⟩
abbrev endFreeGrabInSize : UInt256 := ⟨196⟩
abbrev endFreeGrabOutSize : UInt256 := ⟨0⟩
abbrev endFreeGrabEndPtr : UInt256 := ⟨324⟩

abbrev endFreeUrnInkWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endFreeUrnArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev endFreeStoreVatUrn (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFreeStore I).insert "vatUrn"
    (.tuple [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
      .int (Int.ofNat (endFreeUrnArtWord out).toNat)])

abbrev endFreeStoreInk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFreeStoreVatUrn I out).insert "ink"
    (.int (Int.ofNat (endFreeUrnInkWord out).toNat))

abbrev endFreeStoreArt (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFreeStoreInk I out).insert "art"
    (.int (Int.ofNat (endFreeUrnArtWord out).toNat))

abbrev endFreeStoreGrab (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endFreeStoreArt I out).insert "_grab" (collapseReturns [])

abbrev endFreeGrabDinkWord (out : ByteArray) : UInt256 :=
  UInt256.sub ⟨0⟩ (endFreeUrnInkWord out)

abbrev endFreeUrnsCallStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
    [.var "ilk", sender] "vatUrn"

abbrev endFreeAfterUrnsStmts : List Stmt :=
  [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
    .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
    .require (.binary .eq (.var "art") (.intLit 0)),
    .require (.binary .le (.var "ink") (.intLit int256Limit)) ] ++
  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
    [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
      .intLit 0] "_grab"

noncomputable def endFreeUrnsSelectorMem (mem : ByteArray) : ByteArray :=
  endFreeUrnsSelectorShifted.toByteArray.write 0 mem endFreeUrnsOutPtr.toNat 32

noncomputable def endFreeUrnsArg0Mem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (endFreeIlkWord I).toByteArray.write 0 (endFreeUrnsSelectorMem mem)
    (endFreeUrnsOutPtr + ⟨4⟩).toNat 32

noncomputable def endFreeUrnsCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (endFreeUrnsArg0Mem I mem)
    (endFreeUrnsOutPtr + ⟨36⟩).toNat 32

noncomputable def endFreeUrnsPostCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endFreeUrnsCalldataMem I solcFreePtrMem) endFreeUrnsOutPtr.toNat
    (min 64 out.size)

def endFreeGrabWrites (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    List (Nat × UInt256) :=
  [ (128, endFreeGrabSelectorShifted),
    (132, endFreeIlkWord I),
    (164, solcSourceWord I),
    (196, solcSourceWord I),
    (228, endPackVowWord σ I),
    (260, endFreeGrabDinkWord out),
    (292, ⟨0⟩) ]

noncomputable def endFreeGrabCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  writeCascade (endFreeUrnsPostCallMem I out) (endFreeGrabWrites σ I out)

noncomputable def endFreeGrabMem1 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted

noncomputable def endFreeGrabMem2 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem1 I out) 132 (endFreeIlkWord I)

noncomputable def endFreeGrabMem3 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem2 I out) 164 (solcSourceWord I)

noncomputable def endFreeGrabMem4 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem3 I out) 196 (solcSourceWord I)

noncomputable def endFreeGrabMem5 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem4 I out) 228 (endPackVowWord σ I)

noncomputable def endFreeGrabMem6 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem5 σ I out) 260 (endFreeGrabDinkWord out)

noncomputable def endFreeGrabMem7 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  writeWord (endFreeGrabMem6 σ I out) 292 ⟨0⟩

noncomputable def endFreeGrabPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) : ByteArray :=
  ret.write 0 (endFreeGrabCalldataMem σ I out) endFreeGrabOutPtr.toNat
    (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endFreeLogDataMem (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) : ByteArray :=
  (endFreeUrnInkWord out).toByteArray.write 0 (endFreeGrabPostCallMem σ I out ret) 128 32

theorem endFreeGrabMem7_eq (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    endFreeGrabMem7 σ I out = endFreeGrabCalldataMem σ I out := by
  rfl

private theorem endFreeWordOfIntNeg_toNat (i : Int) (hneg : i < 0)
    (hle : i.natAbs < EVM.wordModulus) :
    (EVM.wordOfInt i).toNat = UInt256.size - i.natAbs := by
  have hdiffPos : i.natAbs ≠ 0 := by
    intro h
    have : i = 0 := by omega
    omega
  have hpos : 0 < i.natAbs := Nat.pos_of_ne_zero hdiffPos
  unfold EVM.wordOfInt
  rw [if_pos hneg]
  rw [Nat.mod_eq_of_lt hle, if_neg hdiffPos]
  change (UInt256.ofNat (EVM.wordModulus - i.natAbs)).toNat = UInt256.size - i.natAbs
  rw [ulit_toNat']
  · rw [show EVM.wordModulus = UInt256.size by decide +native]
  · rw [show EVM.wordModulus = UInt256.size by decide +native]
    exact Nat.sub_lt (by decide +native : 0 < UInt256.size) hpos

theorem endFreeWordOfInt_neg_ofNat_toNat (w : UInt256) (hle : w.toNat ≤ 2 ^ 255) :
    EVM.wordOfInt (-(Int.ofNat w.toNat)) = UInt256.sub ⟨0⟩ w := by
  by_cases hz0 : w.toNat = 0
  · have hw : w = ⟨0⟩ := by
      apply u256_inj
      exact hz0
    subst hw
    rw [u256_sub_self]
    rfl
  · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hz0
    apply u256_inj
    rw [endFreeWordOfIntNeg_toNat]
    · rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos]
      have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by simp
      rw [habs]
      norm_num
    · have hcastPos : (0 : Int) < Int.ofNat w.toNat := by
        simpa using (Int.ofNat_lt.mpr hpos)
      exact neg_neg_of_pos hcastPos
    · have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by simp
      rw [habs]
      exact lt_of_le_of_lt hle (by decide +native : 2 ^ 255 < EVM.wordModulus)

theorem endFreeUrnsSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (endFreeUrnsSelectorMem mem).size = 160 := by
  unfold endFreeUrnsSelectorMem
  exact toByteArray_write32_size_of_ge mem endFreeUrnsSelectorShifted
    endFreeUrnsOutPtr.toNat 96 160 hmem (by decide +native) (by decide +native)
    (by decide +native)

theorem endFreeUrnsSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFreeUrnsSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeUrnsSelectorMem
  rw [toByteArray_write_read_below_of_gap endFreeUrnsSelectorShifted mem
    endFreeUrnsOutPtr.toNat 64 (by rw [hmem]) (by decide +native)
    (by rw [hmem]; decide +native), hread64]

theorem endFreeUrnsArg0Mem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsArg0Mem I mem).size = 164 := by
  unfold endFreeUrnsArg0Mem
  exact toByteArray_write32_size_of_le (endFreeUrnsSelectorMem mem) (endFreeIlkWord I)
    132 160 164 (endFreeUrnsSelectorMem_size hmem)
    (by rw [endFreeUrnsSelectorMem_size hmem]; omega) (by omega)

theorem endFreeUrnsArg0Mem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFreeUrnsArg0Mem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeUrnsArg0Mem
  change ((endFreeIlkWord I).toByteArray.write 0 (endFreeUrnsSelectorMem mem) 132
      32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endFreeUrnsSelectorMem_size hmem]; omega) (by omega),
    endFreeUrnsSelectorMem_read64 hmem hread64]

theorem endFreeUrnsCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsCalldataMem I mem).size = 196 := by
  unfold endFreeUrnsCalldataMem
  exact toByteArray_write32_size_of_ge (endFreeUrnsArg0Mem I mem) (solcSourceWord I)
    164 164 196 (endFreeUrnsArg0Mem_size I hmem)
    (by omega) (by decide +native) (by omega)

theorem endFreeUrnsCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (endFreeUrnsCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeUrnsCalldataMem
  change ((solcSourceWord I).toByteArray.write 0 (endFreeUrnsArg0Mem I mem)
      164 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap (solcSourceWord I)
    (endFreeUrnsArg0Mem I mem) 164 64
    (by rw [endFreeUrnsArg0Mem_size I hmem]; decide +native)
    (by decide +native) (by rw [endFreeUrnsArg0Mem_size I hmem]; decide +native),
    endFreeUrnsArg0Mem_read64 I hmem hread64]

theorem endFreeUrnsPostCallMem_size (I : ExecutionEnv) (out : ByteArray) :
    (endFreeUrnsPostCallMem I out).size = 196 := by
  unfold endFreeUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by decide +native]
  by_cases hlen0 : min 64 out.size = 0
  · rw [hlen0, byteArray_write_len_zero, endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
  · rw [write_eq_gen out (endFreeUrnsCalldataMem I solcFreePtrMem)
      128 (min 64 out.size) hlen0
      (Nat.min_le_right _ _)
      (by
        rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
        have hle64 : min 64 out.size ≤ 64 := Nat.min_le_left _ _
        omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    have hle64 : min 64 out.size ≤ 64 := Nat.min_le_left _ _
    have hleout : min 64 out.size ≤ out.size := Nat.min_le_right _ _
    omega

theorem endFreeUrnsPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endFreeUrnsPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by decide +native]
  by_cases hlen0 : min 64 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endFreeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64
  · rw [write_read_below_gen out (endFreeUrnsCalldataMem I solcFreePtrMem)
      128 (min 64 out.size) 64 hlen0
      (Nat.min_le_right _ _)
      (by
        rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
        have hle64 : min 64 out.size ≤ 64 := Nat.min_le_left _ _
        omega)
      (by decide +native)]
    exact endFreeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64

theorem endFreeGrabCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).size = 324 := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
    [ (128, endFreeGrabSelectorShifted),
      (132, endFreeIlkWord I),
      (164, solcSourceWord I),
      (196, solcSourceWord I),
      (228, endPackVowWord σ I),
      (260, endFreeGrabDinkWord out),
      (292, ⟨0⟩) ]
    (endFreeUrnsPostCallMem_size I out)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endFreeGrabCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_read_preserved_of_base (endFreeUrnsPostCallMem I out)
    [ (128, endFreeGrabSelectorShifted),
      (132, endFreeIlkWord I),
      (164, solcSourceWord I),
      (196, solcSourceWord I),
      (228, endPackVowWord σ I),
      (260, endFreeGrabDinkWord out),
      (292, ⟨0⟩) ]
    (endFreeUrnsPostCallMem_size I out) (by simp [WindowDisjointFromWrites])]
  exact endFreeUrnsPostCallMem_read64 I out

theorem endFreeGrabPostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) :
    endFreeGrabPostCallMem σ I out ret = endFreeGrabCalldataMem σ I out := by
  unfold endFreeGrabPostCallMem
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endFreeGrabOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret (endFreeGrabCalldataMem σ I out)
    0 endFreeGrabOutPtr.toNat

theorem endFreeGrabCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 128 4 = grabSelector := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_read_window_of_head (endFreeUrnsPostCallMem I out)
    128 0 4 endFreeGrabSelectorShifted
    [ (132, endFreeIlkWord I),
      (164, solcSourceWord I),
      (196, solcSourceWord I),
      (228, endPackVowWord σ I),
      (260, endFreeGrabDinkWord out),
      (292, ⟨0⟩) ]]
  · unfold endFreeGrabSelectorShifted grabSelector selectorBytes
    decide +native
  · rw [endFreeUrnsPostCallMem_size I out]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endFreeGrabCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 132 32 =
      (endFreeIlkWord I).toByteArray := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
    (word := endFreeIlkWord I)
    (rest :=
      [ (164, solcSourceWord I),
        (196, solcSourceWord I),
        (228, endPackVowWord σ I),
        (260, endFreeGrabDinkWord out),
        (292, ⟨0⟩) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endFreeUrnsPostCallMem_size I out]
        decide +native)
    (hgap := by
      rw [endFreeUrnsPostCallMem_size I out]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 164 32 =
      (solcSourceWord I).toByteArray := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
      132 (endFreeIlkWord I))
    (word := solcSourceWord I)
    (rest :=
      [ (196, solcSourceWord I),
        (228, endPackVowWord σ I),
        (260, endFreeGrabDinkWord out),
        (292, ⟨0⟩) ])
    (hbase := by
      change (writeCascade (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I)]).size = 196
      exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I)]
        (endFreeUrnsPostCallMem_size I out)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 196 32 =
      (solcSourceWord I).toByteArray := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
        132 (endFreeIlkWord I))
      164 (solcSourceWord I))
    (word := solcSourceWord I)
    (rest :=
      [ (228, endPackVowWord σ I),
        (260, endFreeGrabDinkWord out),
        (292, ⟨0⟩) ])
    (hbase := by
      change (writeCascade (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I)]).size = 196
      exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I)]
        (endFreeUrnsPostCallMem_size I out)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read228_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 228 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
          132 (endFreeIlkWord I))
        164 (solcSourceWord I))
      196 (solcSourceWord I))
    (word := endPackVowWord σ I)
    (rest := [ (260, endFreeGrabDinkWord out), (292, ⟨0⟩) ])
    (hbase := by
      change (writeCascade (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I)]).size = 228
      exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I)]
        (endFreeUrnsPostCallMem_size I out)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read260_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 260 32 =
      (endFreeGrabDinkWord out).toByteArray := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
            132 (endFreeIlkWord I))
          164 (solcSourceWord I))
        196 (solcSourceWord I))
      228 (endPackVowWord σ I))
    (word := endFreeGrabDinkWord out)
    (rest := [ (292, ⟨0⟩) ])
    (hbase := by
      change (writeCascade (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I),
          (228, endPackVowWord σ I)]).size = 260
      exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I),
          (228, endPackVowWord σ I)]
        (endFreeUrnsPostCallMem_size I out)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read292_32 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 292 32 =
      UInt256.toByteArray ⟨0⟩ := by
  unfold endFreeGrabCalldataMem endFreeGrabWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord
              (writeWord (endFreeUrnsPostCallMem I out) 128 endFreeGrabSelectorShifted)
              132 (endFreeIlkWord I))
            164 (solcSourceWord I))
          196 (solcSourceWord I))
        228 (endPackVowWord σ I))
      260 (endFreeGrabDinkWord out))
    (word := (⟨0⟩ : UInt256))
    (rest := [])
    (hbase := by
      change (writeCascade (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I),
          (228, endPackVowWord σ I), (260, endFreeGrabDinkWord out)]).size = 292
      exact writeCascade_size_of_base (endFreeUrnsPostCallMem I out)
        [(128, endFreeGrabSelectorShifted), (132, endFreeIlkWord I),
          (164, solcSourceWord I), (196, solcSourceWord I),
          (228, endPackVowWord σ I), (260, endFreeGrabDinkWord out)]
        (endFreeUrnsPostCallMem_size I out)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endFreeGrabCalldataMem_read128_196 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFreeGrabCalldataMem σ I out).readWithPadding 128 196 =
      grabSelector ++
        (endFreeIlkWord I).toByteArray ++
        (solcSourceWord I).toByteArray ++
        (solcSourceWord I).toByteArray ++
        (endPackVowWord σ I).toByteArray ++
        (endFreeGrabDinkWord out).toByteArray ++
        UInt256.toByteArray ⟨0⟩ := by
  have hsize : (endFreeGrabCalldataMem σ I out).size = 324 :=
    endFreeGrabCalldataMem_size σ I out
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 128 4 192
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 132 32 160
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 164 32 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 196 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 228 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endFreeGrabCalldataMem σ I out) 260 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endFreeGrabCalldataMem_read128_4 σ I out,
    endFreeGrabCalldataMem_read132_32 σ I out,
    endFreeGrabCalldataMem_read164_32 σ I out,
    endFreeGrabCalldataMem_read196_32 σ I out,
    endFreeGrabCalldataMem_read228_32 σ I out,
    endFreeGrabCalldataMem_read260_32 σ I out,
    endFreeGrabCalldataMem_read292_32 σ I out]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endFreeGrabEncode_eq (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr σ I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0] =
      some ((endFreeGrabCalldataMem σ I out).readWithPadding
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat) := by
  change config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address I.source,
        .address I.source,
        .address (endPackVowAddr σ I),
        .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
        .int 0] =
    some ((endFreeGrabCalldataMem σ I out).readWithPadding 128 196)
  rw [endFreeGrabCalldataMem_read128_196 σ I out]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endFreeIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) hsz36
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endFreeIlkWord I := by
      simpa [endBytes32ArgBytes, endFreeIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hsourceWord : EVM.word ↑I.source = solcSourceWord I := by
    change UInt256.ofNat I.source.val = solcSourceWord I
    rfl
  have hvowCanon : (endPackVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I)
  have hvowVal :
      (endPackVowAddr σ I).val = (endPackVowWord σ I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  have hvowWord : EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I := by
    change UInt256.ofNat (endPackVowAddr σ I).val = endPackVowWord σ I
    rw [hvowVal]
    exact u256_ofNat_toNat _
  let inkNat := (endFreeUrnInkWord out).toNat
  have hdinkWord :
      EVM.wordOfInt (-(Int.ofNat (endFreeUrnInkWord out).toNat)) =
        endFreeGrabDinkWord out :=
    endFreeWordOfInt_neg_ofNat_toNat (endFreeUrnInkWord out) hink
  have hdinkWordCast :
      EVM.wordOfInt (-((endFreeUrnInkWord out).toNat : Int)) =
        endFreeGrabDinkWord out := by
    simpa using hdinkWord
  have hdinkBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤
          -(Int.ofNat (endFreeUrnInkWord out).toNat) ∧
        -(Int.ofNat (endFreeUrnInkWord out).toNat) <
          Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor
    · apply neg_le_neg
      exact Int.ofNat_le.mpr (by simpa [EVM.twoPow] using hink)
    · have hnonpos : -(Int.ofNat (endFreeUrnInkWord out).toNat) ≤ 0 := by
        exact neg_nonpos.mpr (Int.natCast_nonneg _)
      exact lt_of_le_of_lt hnonpos (by norm_num [EVM.twoPow])
  have hzeroBounds :
      -(Int.ofNat (EVM.twoPow (256 - 1))) ≤ (0 : Int) ∧
        (0 : Int) < Int.ofNat (EVM.twoPow (256 - 1)) := by
    constructor <;> norm_num [EVM.twoPow]
  have hdinkBoundsSimp :
      (endFreeUrnInkWord out).toNat ≤ EVM.twoPow 255 ∧
        -(Int.ofNat (endFreeUrnInkWord out).toNat) < Int.ofNat (EVM.twoPow 255) := by
    constructor
    · simpa [EVM.twoPow] using hink
    · simpa [EVM.twoPow] using hdinkBounds.2
  have hdinkUpper :
      -(Int.ofNat (endFreeUrnInkWord out).toNat) < Int.ofNat (EVM.twoPow 255) :=
    hdinkBoundsSimp.2
  have hdinkUpperCast :
      -((endFreeUrnInkWord out).toNat : Int) < (EVM.twoPow 255 : Int) := by
    simpa using hdinkUpper
  have hzeroPos : 0 < EVM.twoPow 255 := by
    norm_num [EVM.twoPow]
  have hbytesLen : (EVM.Word.toBytesBE (endFreeIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endFreeIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, grabSelector, selectorBytes, hbytes, hbytesLen, hsourceWord, hvowWord,
    hdinkBoundsSimp, hzeroPos, wordOfInt_zero, zeroBytes]
  rw [if_pos hdinkUpperCast]
  simp [hdinkWordCast, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem endFreeGrabPostCallMem_size (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) :
    (endFreeGrabPostCallMem σ I out ret).size = 324 := by
  rw [endFreeGrabPostCallMem_eq]
  exact endFreeGrabCalldataMem_size σ I out

theorem endFreeGrabPostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) :
    (endFreeGrabPostCallMem σ I out ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endFreeGrabPostCallMem_eq]
  exact endFreeGrabCalldataMem_read64 σ I out

theorem endFreeLogDataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) :
    (endFreeLogDataMem σ I out ret).size = 324 := by
  unfold endFreeLogDataMem
  rw [endFreeGrabPostCallMem_eq]
  exact toByteArray_write32_size_of_le (endFreeGrabCalldataMem σ I out)
    (endFreeUrnInkWord out) 128 324 324
    (endFreeGrabCalldataMem_size σ I out)
    (by rw [endFreeGrabCalldataMem_size σ I out]; omega) (by omega)

theorem endFreeLogDataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out ret : ByteArray) :
    (endFreeLogDataMem σ I out ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFreeLogDataMem
  rw [toByteArray_write_read_below_of_gap (endFreeUrnInkWord out)
    (endFreeGrabPostCallMem σ I out ret) 128 64
    (by rw [endFreeGrabPostCallMem_eq, endFreeGrabCalldataMem_size σ I out]; omega)
    (by omega)
    (by rw [endFreeGrabPostCallMem_eq, endFreeGrabCalldataMem_size σ I out]; decide +native)]
  exact endFreeGrabPostCallMem_read64 σ I out ret

theorem endFreeUrnsPostCallMem_read128_32 (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) :
    (endFreeUrnsPostCallMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold endFreeUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by decide +native]
  rw [show min 64 out.size = 64 from Nat.min_eq_left hlo]
  rw [write_eq_gen out (endFreeUrnsCalldataMem I solcFreePtrMem) 128 64
    (by decide) (by omega)
    (by rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]; omega)]
  rw [readWithPadding_eq_extract _ 128 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endFreeUrnsCalldataMem I solcFreePtrMem).size - 0 = 128 by
    rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 0 = 0 by omega, show min (0 + 32) 64 = 32 by omega]

theorem endFreeUrnsPostCallMem_read160_32 (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) :
    (endFreeUrnsPostCallMem I out).readWithPadding 160 32 =
      out.extract 32 64 := by
  unfold endFreeUrnsPostCallMem
  rw [show endFreeUrnsOutPtr.toNat = 128 by decide +native]
  rw [show min 64 out.size = 64 from Nat.min_eq_left hlo]
  rw [write_eq_gen out (endFreeUrnsCalldataMem I solcFreePtrMem) 128 64
    (by decide) (by omega)
    (by rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]; omega)]
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_extract]; omega)]
  rw [ByteArray.size_extract]
  rw [show min 128 (endFreeUrnsCalldataMem I solcFreePtrMem).size - 0 = 128 by
    rw [endFreeUrnsCalldataMem_size I solcFreePtrMem_size]
    omega]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 64 = 64 by omega]

theorem endFreeUrnsPostCallMem_mload128 (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endFreeUrnsPostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endFreeUrnsPostCallMem I out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      endFreeUrnInkWord out := by
  rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
  rw [endFreeUrnsPostCallMem_size I out, endFreeUrnsPostCallMem_read128_32 I out hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else endFreeUrnInkWord out) =
    endFreeUrnInkWord out
  simp

theorem endFreeUrnsPostCallMem_mload160 (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endFreeUrnsPostCallMem I out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endFreeUrnsPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      endFreeUrnArtWord out := by
  rw [show (⟨160⟩ : UInt256).toNat = 160 by decide]
  rw [endFreeUrnsPostCallMem_size I out, endFreeUrnsPostCallMem_read160_32 I out hlo]
  change (if False ∨ False then (⟨0⟩ : UInt256) else endFreeUrnArtWord out) =
    endFreeUrnArtWord out
  simp

theorem endFreeUrnsWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFreeUrnsOutSize (UInt256.ofNat out.size)).toNat = min 64 out.size := by
  change (min (UInt256.ofNat 64) (UInt256.ofNat out.size)).toNat = min 64 out.size
  by_cases hle : 64 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 64 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 64)]
    exact umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hlt hout

theorem endFreeUrnsCalldataMem_read128_4 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsCalldataMem I mem).readWithPadding 128 4 = urnsSelector := by
  unfold endFreeUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by decide +native]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [endFreeUrnsArg0Mem_size I hmem]) (by omega)
    (by rw [endFreeUrnsArg0Mem_size I hmem]; omega) (by omega) (by norm_num)]
  unfold endFreeUrnsArg0Mem
  rw [show (endFreeUrnsOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [endFreeUrnsSelectorMem_size hmem]; omega) (by omega)
    (by rw [endFreeUrnsSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
  unfold endFreeUrnsSelectorMem endFreeUrnsOutPtr
  change
    (endFreeUrnsSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
      urnsSelector
  rw [toByteArray_write_read_window_of_gap endFreeUrnsSelectorShifted mem 128 0 4
    (by omega) (by omega) (by omega) (by rw [hmem]; decide +native)]
  unfold endFreeUrnsSelectorShifted urnsSelector selectorBytes
  decide +native

theorem endFreeUrnsCalldataMem_read132_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsCalldataMem I mem).readWithPadding 132 32 =
      (endFreeIlkWord I).toByteArray := by
  unfold endFreeUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by decide +native]
  rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
    (by rw [endFreeUrnsArg0Mem_size I hmem]) (by omega)
    (by rw [endFreeUrnsArg0Mem_size I hmem]) (by omega) (by norm_num)]
  unfold endFreeUrnsArg0Mem
  rw [show (endFreeUrnsOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
    (by rw [endFreeUrnsSelectorMem_size hmem]; omega) (by omega) (by omega)
    (by norm_num)]
  rw [toByteArray_extract_all]

theorem endFreeUrnsCalldataMem_read164_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsCalldataMem I mem).readWithPadding 164 32 =
      (solcSourceWord I).toByteArray := by
  unfold endFreeUrnsCalldataMem
  rw [show (endFreeUrnsOutPtr + ⟨36⟩).toNat = 164 by decide +native]
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [endFreeUrnsArg0Mem_size I hmem])]
  rw [toByteArray_extract_all]

theorem endFreeUrnsCalldataMem_read128_68 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (endFreeUrnsCalldataMem I mem).readWithPadding 128 68 =
      urnsSelector ++ (endFreeIlkWord I).toByteArray ++ (solcSourceWord I).toByteArray := by
  have hsize : (endFreeUrnsCalldataMem I mem).size = 196 :=
    endFreeUrnsCalldataMem_size I hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (endFreeUrnsCalldataMem I mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endFreeUrnsCalldataMem I mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endFreeUrnsCalldataMem_read128_4 I hmem,
    endFreeUrnsCalldataMem_read132_32 I hmem,
    endFreeUrnsCalldataMem_read164_32 I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endFreeUrnsEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hsz36 : 36 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "urns"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] =
      some ((endFreeUrnsCalldataMem I mem).readWithPadding
        endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat) := by
  change config.externalABI.encode? "urns"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] =
    some ((endFreeUrnsCalldataMem I mem).readWithPadding 128 68)
  rw [endFreeUrnsCalldataMem_read128_68 I hmem]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endFreeIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) hsz36
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endFreeIlkWord I := by
      simpa [endBytes32ArgBytes, endFreeIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hsourceWord : EVM.word ↑I.source = solcSourceWord I := by
    change UInt256.ofNat I.source.val = solcSourceWord I
    rfl
  have hbytesLen : (EVM.Word.toBytesBE (endFreeIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endFreeIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, urnsSelector,
    selectorBytes, hbytes, hbytesLen, hsourceWord, zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

theorem endFree_bytesToWord_drop32_eq_extract32_64 (out : ByteArray) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = endFreeUrnArtWord out := by
  unfold endFreeUrnArtWord
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract 32 64), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]

theorem endFreeUrnsDecode_ok_aux {out : ByteArray} (hlo : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      some [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
        .int (Int.ofNat (endFreeUrnArtWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hword1 := endFree_bytesToWord_drop32_eq_extract32_64 out
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 0) htake0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 32) htake32]
  simp only [Option.bind_some]
  have hword0' :
      ABI.bytesToWord ((out.toList.drop 0).take 32) = endFreeUrnInkWord out := by
    simpa [endFreeUrnInkWord, List.drop_zero] using hword0
  rw [hword0', hword1]

theorem endFreeUrnsDecode_ok {out : ByteArray} (hlo : 64 ≤ out.size) :
    config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
        .int (Int.ofNat (endFreeUrnArtWord out).toNat)] := by
  have h := endFreeUrnsDecode_ok_aux (out := out) hlo
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endFreeUrnsDecode_none_short_aux {out : ByteArray} (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 32) htake32n]
    simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp

theorem endFreeUrnsDecode_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "urns" out = none := by
  have h := endFreeUrnsDecode_none_short_aux (out := out) hshort
  simpa [config, externalABI, uint256, uint256Int, abiUInt256] using h

theorem endFree_solcErrorStringMem0_size_of_size196 {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem0 mem).size = 196 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem endFree_solcErrorStringMem1_size_of_size196 {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem1 mem).size = 196 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endFree_solcErrorStringMem0_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endFree_solcErrorStringMem0_size_of_size196 hmem]

theorem endFree_solcErrorStringMem2_size_of_size196 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 196) :
    (solcErrorStringMem2 len mem).size = 196 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endFree_solcErrorStringMem1_size_of_size196 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endFree_solcErrorStringMem1_size_of_size196 hmem]

theorem endFree_solcErrorStringMem3_size_of_size196 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 196) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endFree_solcErrorStringMem2_size_of_size196 len hmem])]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endFree_solcErrorStringMem2_size_of_size196 len hmem]

theorem endFree_solcErrorStringMem3_read64_of_size196 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [endFree_solcErrorStringMem2_size_of_size196 len hmem]; omega) (by omega)
      (by
        rw [endFree_solcErrorStringMem2_size_of_size196 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [endFree_solcErrorStringMem1_size_of_size196 hmem]; omega) (by omega)
      (by
        rw [endFree_solcErrorStringMem1_size_of_size196 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [endFree_solcErrorStringMem0_size_of_size196 hmem]; omega) (by omega)
      (by
        rw [endFree_solcErrorStringMem0_size_of_size196 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem endFree_solcErrorStringMem3_mload64_of_size196 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [endFree_solcErrorStringMem3_size_of_size196 len word hmem]; decide)
    (by decide) (endFree_solcErrorStringMem3_read64_of_size196 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem endFree_solcErrorStringRevertTail_aw7 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 7) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 7)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 7)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hdMload
      mem_cost
      (endFree_solcErrorStringMem3_mload64_of_size196 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

abbrev endFreeLiveEvaledRef : EvaledStorageRef :=
  { base := "live", steps := [] }

theorem endFreeLocals_get_live (I : ExecutionEnv) :
    (endFreeStore I).get? "live" = none := by
  simp [endFreeStore, endFreeIlkValue]

theorem evalStorageRef_endFree_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endFreeStore I } evm
      liveRef = .ok endFreeLiveEvaledRef := by
  simp [endFreeLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
    pure, bind]

theorem evalExpr_endFree_live_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm
        (.storage liveRef) = .ok (.int 0) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFreeStore I })
      (slot := liveRef)
      (er := endFreeLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 0)
      (hbase := endFreeLocals_get_live I)
      (her := evalStorageRef_endFree_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endFree_live_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFreeStore I })
      (slot := liveRef)
      (er := endFreeLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := endFreeLocals_get_live I)
      (her := evalStorageRef_endFree_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 0 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 0) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 0) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem endEvalExpr_le_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hle]

theorem endEvalExpr_le_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : b < a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .le lhs rhs) =
      .ok (.bool false) := by
  have hnot : ¬ a ≤ b := by omega
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hnot]

theorem endFreeStore_get_ilk (I : ExecutionEnv) :
    (endFreeStore I).get? "ilk" = some (endFreeIlkValue I) := by
  rw [endFreeStore, store_get_self]

theorem endEvalExpr_varFixedBytes {evm : EVM.State} {locals : Store}
    {name : Ident} {n : Fin 32} {bytes : List UInt8}
    (h : locals.get? name = some (.fixedBytes n bytes)) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.fixedBytes n bytes) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.fixedBytes n bytes)
  rw [h]
  rfl

theorem evalExpr_endFree_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm (.var "ilk") =
      .ok (endFreeIlkValue I) := by
  simpa [endFreeIlkValue] using
    endEvalExpr_varFixedBytes (evm := evm) (locals := endFreeStore I)
      (name := "ilk") (n := bytes32Width) (bytes := endBytes32ArgBytes I)
      (endFreeStore_get_ilk I)

theorem evalExprs_endFree_urnsArgs (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExprs? config { contract := contract, locals := endFreeStore I } evm
      [.var "ilk", sender] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] := by
  have hilk := evalExpr_endFree_ilk evm I
  have hsender :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm sender =
        .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExprs?, hilk, hsender, endFreeIlkValue, EvalResult.bind, bind, pure]

theorem endFreeSourceLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
    intro hbad
    apply hlive
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endFree_live_zero_false evm0 I hliveLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [freeTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endFreeStore I })
      (evm := evm0)
      (guard := .binary .eq (.storage liveRef) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage vatRef) "urns" (.intLit 0)
          [.var "ilk", sender] "vatUrn" ++
        [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .require (.binary .eq (.var "art") (.intLit 0)),
          .require (.binary .le (.var "ink") (.intLit int256Limit)) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0] "_grab")
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endFreeBodyReverts_urnsNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSlotWord, solcSlotWord] using hlive
  have hguardLive :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFree_live_zero_true evm0 I hliveLoad
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFreeStore I).get? "vat" = none := by
      simp [endFreeStore, endFreeIlkValue]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endPackVatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardUrns :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hurnsBlock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        endFreeUrnsCallStmts .reverted := by
    simpa [endFreeUrnsCallStmts, checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm0)
        (locals := endFreeStore I) (receiver := .storage vatRef)
        (retVar := "vatUrn") (name := "urns") (sendVal := 0)
        (args := [.var "ilk", sender]) (perm := true)
        hguardUrns
  have hurnsWithTail :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (endFreeUrnsCallStmts ++ endFreeAfterUrnsStmts) .reverted := by
    exact execBlock_append_term
      (s2 := endFreeAfterUrnsStmts) hurnsBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    simp only [freeTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    simpa [endFreeUrnsCallStmts, endFreeAfterUrnsStmts] using hurnsWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReverts_urnsCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (false, evmUrns, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSlotWord, solcSlotWord] using hlive
  have hguardLive :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFree_live_zero_true evm0 I hliveLoad
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFreeStore I).get? "vat" = none := by
      simp [endFreeStore, endFreeIlkValue]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardUrns :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endFreeStore I } evm0
        [.var "ilk", sender] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] :=
    evalExprs_endFree_urnsArgs evm0 I (by simp [evm0, initState])
  have hurnsBlock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        endFreeUrnsCallStmts .reverted := by
    simpa [endFreeUrnsCallStmts, checkedExternalCallStmts] using
      checkedExternalCallFailure
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmUrns)
        (locals := endFreeStore I) (receiver := .storage vatRef)
        (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
        (sendVal := 0) (args := [.var "ilk", sender])
        (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source])
        (out := out) (perm := true)
        hguardUrns hreceiver hargs (by simpa [evm0] using hcall)
  have hurnsWithTail :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (endFreeUrnsCallStmts ++ endFreeAfterUrnsStmts) .reverted := by
    exact execBlock_append_term
      (s2 := endFreeAfterUrnsStmts) hurnsBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    simp only [freeTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    simpa [endFreeUrnsCallStmts, endFreeAfterUrnsStmts] using hurnsWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReverts_urnsDecodeShort {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hshort : out.size < 64) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSlotWord, solcSlotWord] using hlive
  have hguardLive :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFree_live_zero_true evm0 I hliveLoad
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFreeStore I).get? "vat" = none := by
      simp [endFreeStore, endFreeIlkValue]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardUrns :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endFreeStore I } evm0
        [.var "ilk", sender] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] :=
    evalExprs_endFree_urnsArgs evm0 I (by simp [evm0, initState])
  have hurnsBlock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        endFreeUrnsCallStmts .reverted := by
    simpa [endFreeUrnsCallStmts, checkedExternalCallStmts] using
      checkedExternalCallDecodeRevert
        (cfg := config) (C := contract) (evm := evm0) (evm' := evmUrns)
        (locals := endFreeStore I) (receiver := .storage vatRef)
        (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
        (sendVal := 0) (args := [.var "ilk", sender])
        (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source])
        (out := out) (perm := true)
        hguardUrns hreceiver hargs (by simpa [evm0] using hcall)
        (endFreeUrnsDecode_none_short hshort)
  have hurnsWithTail :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (endFreeUrnsCallStmts ++ endFreeAfterUrnsStmts) .reverted := by
    exact execBlock_append_term
      (s2 := endFreeAfterUrnsStmts) hurnsBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    simp only [freeTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    simpa [endFreeUrnsCallStmts, endFreeAfterUrnsStmts] using hurnsWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreePrefixUrnsSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endFreeStore I } evm0
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
        endFreeUrnsCallStmts)
      (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
  intro evm0
  have hliveLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSlotWord, solcSlotWord] using hlive
  have hguardLive :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .eq (.storage liveRef) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endFree_live_zero_true evm0 I hliveLoad
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
    have hbase : (endFreeStore I).get? "vat" = none := by
      simp [endFreeStore, endFreeIlkValue]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endPackVatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguardUrns :
      evalExpr? config { contract := contract, locals := endFreeStore I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endFreeStore I } evm0
        [.var "ilk", sender] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source] :=
    evalExprs_endFree_urnsArgs evm0 I (by simp [evm0, initState])
  have hurnsBlock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        endFreeUrnsCallStmts
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmUrns)
      (locals := endFreeStore I) (receiver := .storage vatRef)
      (retVar := "vatUrn") (name := "urns") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk", sender])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source])
      (out := out) (perm := true)
      (value :=
        [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
          .int (Int.ofNat (endFreeUrnArtWord out).toNat)])
      hguardUrns hreceiver hargs (by simpa [evm0] using hcall)
      (endFreeUrnsDecode_ok hlo)
    simpa [endFreeUrnsCallStmts, checkedExternalCallStmts, endFreeStoreVatUrn,
      collapseReturns] using hblock
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
  simpa using hurnsBlock

theorem evalExpr_endFree_vatUrn_ink (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      (.tupleGet (.var "vatUrn") 0) =
        .ok (.int (Int.ofNat (endFreeUrnInkWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endFreeStoreVatUrn I out } evm
        (.var "vatUrn") =
          .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
            .int (Int.ofNat (endFreeUrnArtWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endFreeStoreVatUrn I out).get? "vatUrn") =
        .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
          .int (Int.ofNat (endFreeUrnArtWord out).toNat)])
    rw [endFreeStoreVatUrn, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endFree_vatUrn_art_afterInk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreInk I out } evm
      (.tupleGet (.var "vatUrn") 1) =
        .ok (.int (Int.ofNat (endFreeUrnArtWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endFreeStoreInk I out } evm
        (.var "vatUrn") =
          .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
            .int (Int.ofNat (endFreeUrnArtWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endFreeStoreInk I out).get? "vatUrn") =
        .ok (.tuple [.int (Int.ofNat (endFreeUrnInkWord out).toNat),
          .int (Int.ofNat (endFreeUrnArtWord out).toNat)])
    rw [endFreeStoreInk, store_get_ne _ _ (by decide +native), endFreeStoreVatUrn,
      store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endFree_ink_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
      (.var "ink") = .ok (.int (Int.ofNat (endFreeUrnInkWord out).toNat)) := by
  simpa [endFreeStoreArt, endFreeStoreInk] using
    endEvalExpr_varUInt256 (evm := evm) (locals := endFreeStoreArt I out)
      (name := "ink") (value := endFreeUrnInkWord out)
      (by
        rw [endFreeStoreArt, store_get_ne _ _ (by decide +native)]
        simp [endFreeStoreInk])

theorem evalExpr_endFree_art_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
      (.var "art") = .ok (.int (Int.ofNat (endFreeUrnArtWord out).toNat)) := by
  simpa [endFreeStoreArt] using
    endEvalExpr_varUInt256 (evm := evm) (locals := endFreeStoreArt I out)
      (name := "art") (value := endFreeUrnArtWord out)
      (by simp [endFreeStoreArt])

theorem evalExpr_endFree_ilk_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
      (.var "ilk") = .ok (endFreeIlkValue I) := by
  simpa [endFreeIlkValue] using
    endEvalExpr_varFixedBytes (evm := evm) (locals := endFreeStoreArt I out)
      (name := "ilk") (n := bytes32Width) (bytes := endBytes32ArgBytes I)
      (by
        rw [endFreeStoreArt, store_get_ne _ _ (by decide +native),
          endFreeStoreInk, store_get_ne _ _ (by decide +native),
          endFreeStoreVatUrn, store_get_ne _ _ (by decide +native),
          endFreeStore, store_get_self])

theorem evalExpr_endFree_negInk_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
      (.unary .neg (asInt256 (.var "ink"))) =
        .ok (.int (-(Int.ofNat (endFreeUrnInkWord out).toNat))) := by
  have hink := evalExpr_endFree_ink_afterArt evm I out
  simp only [asInt256, evalExpr?, hink, castValue?, evalUnaryOp?, EvalResult.bind, bind,
    int256St, int256Int]
  rfl

theorem evalExprs_endFree_grabArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hsrc : evm.executionEnv.source = I.source)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config { contract := contract, locals := endFreeStoreArt I out } evm
      [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
        .intLit 0] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0] := by
  have hilk := evalExpr_endFree_ilk_afterArt evm I out
  have hsender :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  have hvow :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        vowAddr = .ok (.address (endPackVowAddr evm.accountMap I)) := by
    have hbase : (endFreeStoreArt I out).get? "vow" = none := by
      simp [endFreeStoreArt, endFreeStoreInk, endFreeStoreVatUrn, endFreeStore]
    simpa [vowAddr, howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow (locals := endFreeStoreArt I out) evm hbase
  have hneg := evalExpr_endFree_negInk_afterArt evm I out
  have hzero :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  simp [evalExprs?, hilk, hsender, hvow, hneg, hzero, endFreeIlkValue,
    EvalResult.bind, bind, pure]

theorem endFreeTailReverts_artNonzero (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hart : endFreeUrnArtWord out ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      endFreeAfterUrnsStmts .reverted := by
  have hinkTuple := evalExpr_endFree_vatUrn_ink evm I out
  have hartTuple := evalExpr_endFree_vatUrn_art_afterInk evm I out
  have hartVar := evalExpr_endFree_art_afterArt evm I out
  have hzero :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hneq : Int.ofNat (endFreeUrnArtWord out).toNat ≠ 0 := by
    intro hbad
    apply hart
    exact uint256_toNat_eq_zero (Int.ofNat.inj hbad)
  have hreq :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_eq_int_false hartVar hzero hneq
  simp only [endFreeAfterUrnsStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hinkTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hartTuple) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hreq)

theorem endFreeTailReverts_inkOverflow (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : 2 ^ 255 < (endFreeUrnInkWord out).toNat) :
    ExecBlock config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      endFreeAfterUrnsStmts .reverted := by
  have hinkTuple := evalExpr_endFree_vatUrn_ink evm I out
  have hartTuple := evalExpr_endFree_vatUrn_art_afterInk evm I out
  have hartVar := evalExpr_endFree_art_afterArt evm I out
  have hzeroArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hartInt : Int.ofNat (endFreeUrnArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  have hreqArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hartVar hzeroArt hartInt
  have hinkVar := evalExpr_endFree_ink_afterArt evm I out
  have hlimitEval :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit int256Limit) = .ok (.int int256Limit) := by
    simp [evalExpr?, pure]
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hltInt : int256Limit < Int.ofNat (endFreeUrnInkWord out).toNat := by
    rw [hlimit]
    exact Int.ofNat_lt.mpr hink
  have hreqInk :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool false) :=
    endEvalExpr_le_int_false hinkVar hlimitEval hltInt
  simp only [endFreeAfterUrnsStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hinkTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hartTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqArt) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hreqInk)

theorem endFreeTailReverts_grabNoCode (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endPackVatWord evm.accountMap I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      endFreeAfterUrnsStmts .reverted := by
  have hinkTuple := evalExpr_endFree_vatUrn_ink evm I out
  have hartTuple := evalExpr_endFree_vatUrn_art_afterInk evm I out
  have hartVar := evalExpr_endFree_art_afterArt evm I out
  have hzeroArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hartInt : Int.ofNat (endFreeUrnArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  have hreqArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hartVar hzeroArt hartInt
  have hinkVar := evalExpr_endFree_ink_afterArt evm I out
  have hlimitEval :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit int256Limit) = .ok (.int int256Limit) := by
    simp [evalExpr?, pure]
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hleInt : Int.ofNat (endFreeUrnInkWord out).toNat ≤ int256Limit := by
    rw [hlimit]
    exact Int.ofNat_le.mpr hink
  have hreqInk :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hinkVar hlimitEval hleInt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.storage vatRef) = .ok (.address (endPackVatAddr evm.accountMap I)) := by
    have hbase : (endFreeStoreArt I out).get? "vat" = none := by
      simp [endFreeStoreArt, endFreeStoreInk, endFreeStoreVatUrn, endFreeStore]
    simpa [howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStoreArt I out) evm hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm.lookupAccount (endPackVatAddr evm.accountMap I)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      endUniswapExtCodeSizeWord_zero_lookup_code_zero
        (σ := evm.accountMap) (target := endPackVatWord evm.accountMap I)
        (addr := endPackVatAddr evm.accountMap I)
        (endPackVatAddr_eq_ofUInt256 evm.accountMap I) hcodeSize
  have hguardGrab :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  have hgrabBlock :
      ExecBlock config { contract := contract, locals := endFreeStoreArt I out } evm
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0] "_grab")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode
        (cfg := config) (C := contract) (evm := evm)
        (locals := endFreeStoreArt I out) (receiver := .storage vatRef)
        (retVar := "_grab") (name := "grab") (sendVal := 0)
        (args :=
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0])
        (perm := true) hguardGrab
  simp only [endFreeAfterUrnsStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hinkTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hartTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqArt) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqInk) ?_
  simpa using hgrabBlock

theorem endFreeTailReverts_grabCallFailed (evm evmGrab : EVM.State) (I : ExecutionEnv)
    (out grabOut : ByteArray)
    (hsrc : evm.executionEnv.source = I.source)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endPackVatWord evm.accountMap I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endPackVatAddr evm.accountMap I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0]
        (false, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      endFreeAfterUrnsStmts .reverted := by
  have hinkTuple := evalExpr_endFree_vatUrn_ink evm I out
  have hartTuple := evalExpr_endFree_vatUrn_art_afterInk evm I out
  have hartVar := evalExpr_endFree_art_afterArt evm I out
  have hzeroArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hartInt : Int.ofNat (endFreeUrnArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  have hreqArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hartVar hzeroArt hartInt
  have hinkVar := evalExpr_endFree_ink_afterArt evm I out
  have hlimitEval :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit int256Limit) = .ok (.int int256Limit) := by
    simp [evalExpr?, pure]
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hleInt : Int.ofNat (endFreeUrnInkWord out).toNat ≤ int256Limit := by
    rw [hlimit]
    exact Int.ofNat_le.mpr hink
  have hreqInk :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hinkVar hlimitEval hleInt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.storage vatRef) = .ok (.address (endPackVatAddr evm.accountMap I)) := by
    have hbase : (endFreeStoreArt I out).get? "vat" = none := by
      simp [endFreeStoreArt, endFreeStoreInk, endFreeStoreVatUrn, endFreeStore]
    simpa [howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStoreArt I out) evm hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endPackVatAddr evm.accountMap I)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap) (target := endPackVatWord evm.accountMap I)
        (addr := endPackVatAddr evm.accountMap I)
        (endPackVatAddr_eq_ofUInt256 evm.accountMap I) hcodeSize
  have hguardGrab :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endFreeStoreArt I out } evm
        [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
          .intLit 0] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0] :=
    evalExprs_endFree_grabArgs evm I out hsrc howner
  have hgrabBlock :
      ExecBlock config { contract := contract, locals := endFreeStoreArt I out } evm
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0] "_grab")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure
        (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
        (locals := endFreeStoreArt I out) (receiver := .storage vatRef)
        (retVar := "_grab") (name := "grab") (target := endPackVatAddr evm.accountMap I)
        (sendVal := 0)
        (args :=
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0])
        (argVals :=
          [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address I.source,
            .address I.source,
            .address (endPackVowAddr evm.accountMap I),
            .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
            .int 0])
        (out := grabOut) (perm := true)
        hguardGrab hreceiver hargs hcall
  simp only [endFreeAfterUrnsStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hinkTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hartTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqArt) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqInk) ?_
  simpa using hgrabBlock

theorem endFreeTailReturns_grabSuccess (evm evmGrab : EVM.State) (I : ExecutionEnv)
    (out grabOut : ByteArray)
    (hsrc : evm.executionEnv.source = I.source)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endPackVatWord evm.accountMap I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endPackVatAddr evm.accountMap I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0]
        (true, evmGrab, grabOut) true) :
    ExecBlock config { contract := contract, locals := endFreeStoreVatUrn I out } evm
      endFreeAfterUrnsStmts
      (.ok { contract := contract, locals := endFreeStoreGrab I out } evmGrab) := by
  have hinkTuple := evalExpr_endFree_vatUrn_ink evm I out
  have hartTuple := evalExpr_endFree_vatUrn_art_afterInk evm I out
  have hartVar := evalExpr_endFree_art_afterArt evm I out
  have hzeroArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hartInt : Int.ofNat (endFreeUrnArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  have hreqArt :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_eq_int_true hartVar hzeroArt hartInt
  have hinkVar := evalExpr_endFree_ink_afterArt evm I out
  have hlimitEval :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.intLit int256Limit) = .ok (.int int256Limit) := by
    simp [evalExpr?, pure]
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hleInt : Int.ofNat (endFreeUrnInkWord out).toNat ≤ int256Limit := by
    rw [hlimit]
    exact Int.ofNat_le.mpr hink
  have hreqInk :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool true) :=
    endEvalExpr_le_int_true hinkVar hlimitEval hleInt
  have hreceiver :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.storage vatRef) = .ok (.address (endPackVatAddr evm.accountMap I)) := by
    have hbase : (endFreeStoreArt I out).get? "vat" = none := by
      simp [endFreeStoreArt, endFreeStoreInk, endFreeStoreVatUrn, endFreeStore]
    simpa [howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vat (locals := endFreeStoreArt I out) evm hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endPackVatAddr evm.accountMap I)).option 0
          (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
        (σ := evm.accountMap) (target := endPackVatWord evm.accountMap I)
        (addr := endPackVatAddr evm.accountMap I)
        (endPackVatAddr_eq_ofUInt256 evm.accountMap I) hcodeSize
  have hguardGrab :
      evalExpr? config { contract := contract, locals := endFreeStoreArt I out } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := endFreeStoreArt I out } evm
        [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
          .intLit 0] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0] :=
    evalExprs_endFree_grabArgs evm I out hsrc howner
  have hgrabBlock :
      ExecBlock config { contract := contract, locals := endFreeStoreArt I out } evm
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
            .intLit 0] "_grab")
        (.ok { contract := contract, locals := endFreeStoreGrab I out } evmGrab) := by
    have hdec : config.externalABI.decode? "grab" grabOut = some [] := by
      simp [config, externalABI, decodeVoid?]
    have hblock := checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
      (locals := endFreeStoreArt I out) (receiver := .storage vatRef)
      (retVar := "_grab") (name := "grab") (target := endPackVatAddr evm.accountMap I)
      (sendVal := 0)
      (args :=
        [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")),
          .intLit 0])
      (argVals :=
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evm.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0])
      (out := grabOut) (perm := true) (value := [])
      hguardGrab hreceiver hargs hcall hdec
    simpa [checkedExternalCallStmts, endFreeStoreGrab, collapseReturns] using hblock
  simp only [endFreeAfterUrnsStmts, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl hinkTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hartTuple) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqArt) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqInk) ?_
  simpa using hgrabBlock

theorem endFreeBodyReverts_artNonzero {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size)
    (hart : endFreeUrnArtWord out ≠ ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
          endFreeUrnsCallStmts)
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    simpa [evm0] using
      endFreePrefixUrnsSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmUrns := evmUrns) (out := out)
        hwv hlive hcodeSize hcall hlo
  have htail := endFreeTailReverts_artNonzero evmUrns I out hart
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    have hseq := execBlock_append
      (s2 := endFreeAfterUrnsStmts) hprefix htail
    simpa [freeTransition, nonpayable, endFreeUrnsCallStmts, endFreeAfterUrnsStmts,
      checkedExternalCallStmts, List.cons_append, List.nil_append, List.append_assoc] using hseq
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReverts_inkOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : 2 ^ 255 < (endFreeUrnInkWord out).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
          endFreeUrnsCallStmts)
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    simpa [evm0] using
      endFreePrefixUrnsSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmUrns := evmUrns) (out := out)
        hwv hlive hcodeSize hcall hlo
  have htail := endFreeTailReverts_inkOverflow evmUrns I out hart hink
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    have hseq := execBlock_append
      (s2 := endFreeAfterUrnsStmts) hprefix htail
    simpa [freeTransition, nonpayable, endFreeUrnsCallStmts, endFreeAfterUrnsStmts,
      checkedExternalCallStmts, List.cons_append, List.nil_append, List.append_assoc] using hseq
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReverts_grabNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size)
    (howner : evmUrns.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hgrabCodeSize :
      Reasoning.Theory.extCodeSizeWord evmUrns.accountMap
        (endPackVatWord evmUrns.accountMap I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
          endFreeUrnsCallStmts)
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    simpa [evm0] using
      endFreePrefixUrnsSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmUrns := evmUrns) (out := out)
        hwv hlive hcodeSize hcall hlo
  have htail :=
    endFreeTailReverts_grabNoCode evmUrns I out howner hart hink hgrabCodeSize
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    have hseq := execBlock_append
      (s2 := endFreeAfterUrnsStmts) hprefix htail
    simpa [freeTransition, nonpayable, endFreeUrnsCallStmts, endFreeAfterUrnsStmts,
      checkedExternalCallStmts, List.cons_append, List.nil_append, List.append_assoc] using hseq
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReverts_grabCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmGrab : EVM.State} {out grabOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size)
    (hsrc : evmUrns.executionEnv.source = I.source)
    (howner : evmUrns.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hgrabCodeSize :
      Reasoning.Theory.extCodeSizeWord evmUrns.accountMap
        (endPackVatWord evmUrns.accountMap I) ≠ ⟨0⟩)
    (hgrabCall :
      typedCallViaEVM config evmUrns
        (EVM.address (endPackVatAddr evmUrns.accountMap I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evmUrns.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0]
        (false, evmGrab, grabOut) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body .reverted := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
          endFreeUrnsCallStmts)
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    simpa [evm0] using
      endFreePrefixUrnsSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmUrns := evmUrns) (out := out)
        hwv hlive hcodeSize hcall hlo
  have htail :=
    endFreeTailReverts_grabCallFailed evmUrns evmGrab I out grabOut hsrc howner hart
      hink hgrabCodeSize hgrabCall
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body .reverted := by
    have hseq := execBlock_append
      (s2 := endFreeAfterUrnsStmts) hprefix htail
    simpa [freeTransition, nonpayable, endFreeUrnsCallStmts, endFreeAfterUrnsStmts,
      checkedExternalCallStmts, List.cons_append, List.nil_append, List.append_assoc] using hseq
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFreeBodyReturns_grabSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmGrab : EVM.State} {out grabOut : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endPackVatAddr σ I)) "urns" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
        (true, evmUrns, out) true)
    (hlo : 64 ≤ out.size)
    (hsrc : evmUrns.executionEnv.source = I.source)
    (howner : evmUrns.executionEnv.codeOwner = I.codeOwner)
    (hart : endFreeUrnArtWord out = ⟨0⟩)
    (hink : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255)
    (hgrabCodeSize :
      Reasoning.Theory.extCodeSizeWord evmUrns.accountMap
        (endPackVatWord evmUrns.accountMap I) ≠ ⟨0⟩)
    (hgrabCall :
      typedCallViaEVM config evmUrns
        (EVM.address (endPackVatAddr evmUrns.accountMap I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address I.source,
          .address I.source,
          .address (endPackVowAddr evmUrns.accountMap I),
          .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
          .int 0]
        (true, evmGrab, grabOut) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endFreeStore I) freeTransition.body
      (.returned { contract := contract, locals := endFreeStoreGrab I out } evmGrab none) := by
  intro evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        (nonpayable ++
          [ .require (.binary .eq (.storage liveRef) (.intLit 0)) ] ++
          endFreeUrnsCallStmts)
        (.ok { contract := contract, locals := endFreeStoreVatUrn I out } evmUrns) := by
    simpa [evm0] using
      endFreePrefixUrnsSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmUrns := evmUrns) (out := out)
        hwv hlive hcodeSize hcall hlo
  have htail :=
    endFreeTailReturns_grabSuccess evmUrns evmGrab I out grabOut hsrc howner hart
      hink hgrabCodeSize hgrabCall
  have hblock :
      ExecBlock config { contract := contract, locals := endFreeStore I } evm0
        freeTransition.body
        (.ok { contract := contract, locals := endFreeStoreGrab I out } evmGrab) := by
    have hseq := execBlock_append
      (s2 := endFreeAfterUrnsStmts) hprefix htail
    simpa [freeTransition, nonpayable, endFreeUrnsCallStmts, endFreeAfterUrnsStmts,
      checkedExternalCallStmts, List.cons_append, List.nil_append, List.append_assoc] using hseq
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockOK hblock

theorem endFreeX_liveZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFreeBodyPc
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7760⟩
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd7693 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd7694raw⟩ := rd7693.sload (by decide +native) (by evm_ov)
  have hraw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨8⟩ ⟨0⟩)) =
        ⟨0⟩ := by
    simpa [endSlotWord, solcSlotWord] using hlive
  have rd7694 := rd7694raw
  rw [hraw] at rd7694
  have rd7695raw := rd7694.iszero (by decide +native) (by evm_ov)
  have rd7695 := rd7695raw
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7695
  have rd7698 := rd7695.push2 ⟨7760⟩ (by decide +native) (by evm_ov)
  have rd7760 := rd7698.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd7760⟩

theorem endFreeX_liveNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endFreeBodyPc
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd7693 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨8⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd7694raw⟩ := rd7693.sload (by decide +native) (by evm_ov)
  have rd7694 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7694⟩
        (endSlotWord ⟨8⟩ σ I :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd7694raw⟩
  obtain ⟨_, _, rd7694⟩ := rd7694
  have rd7695raw := rd7694.iszero (by decide +native) (by evm_ov)
  have hzero : UInt256.isZero (endSlotWord ⟨8⟩ σ I) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hlive
  have rd7695 := rd7695raw
  rw [hzero] at rd7695
  have rd7698 := rd7695.push2 ⟨7760⟩ (by decide +native) (by evm_ov)
  have rd7699 := rd7698.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨7699⟩) (len := ⟨14⟩)
    (rawWord := ⟨0x456e642f7374696c6c2d6c697665⟩) (shift := ⟨144⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f7374696c6c2d6c697665⟩ ⟨144⟩)
    (op := .PUSH14) (width := 14)
    (by simpa using rd7699)
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_urnsExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7760⟩
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7831⟩
      (endPackVatWord σ I :: endPackVatWord σ I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hcallMem :
      (endFreeUrnsCalldataMem I solcFreePtrMem).size = 196 :=
    endFreeUrnsCalldataMem_size I solcFreePtrMem_size
  have hcallRead64 :
      (endFreeUrnsCalldataMem I solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    endFreeUrnsCalldataMem_read64 I solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeUrnsCalldataMem I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeUrnsCalldataMem I solcFreePtrMem).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have hselectorShift :
      UInt256.shiftLeft (⟨0x09092f97⟩ : UInt256) ⟨226⟩ =
        endFreeUrnsSelectorShifted := by
    decide +native
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ I) = endPackVatWord σ I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ I)
  have rd7763 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd7764raw⟩ := rd7763.sload (by decide +native) (by evm_ov)
  have rd7764 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7764⟩
        (endSlotWord ⟨1⟩ σ I :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd7764raw⟩
  obtain ⟨_, _, rd7764⟩ := rd7764
  have rd7831 := evm_run rd7764 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x09092f97⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨226⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (endFreeUrnsSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by decide +native) mem_cost
      (by simp [endFreeUrnsSelectorMem, endFreeUrnsOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeUrnsArg0Mem I solcFreePtrMem) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by simp [endFreeUrnsArg0Mem, endFreeUrnsOutPtr])
      (by decide) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by simp [endFreeUrnsCalldataMem, endFreeUrnsOutPtr])
      (by decide) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 ⟨0x2424be5c⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFreeUrnsSelectorMem, endFreeUrnsArg0Mem, endFreeUrnsCalldataMem,
      endFreeUrnsOutPtr, endFreeUrnsInSize, endFreeUrnsOutSize, endFreeUrnsEndPtr,
      endFreeUrnsSelectorShifted, endFreeUrnsSelectorWord, endPackVatWord, endSlotWord,
      solcSlotWord, solcAddrMask, hselectorShift, hvatMask] using rd7831⟩

theorem endFreeX_urnsNoCode {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7760⟩
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7831⟩ := endFreeX_urnsExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨7831⟩) (okPc := ⟨7843⟩) rd7831
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_urnsCallReady {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7760⟩
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7846⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd7831⟩ := endFreeX_urnsExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd7846⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨7831⟩) (okPc := ⟨7843⟩) rd7831
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd7846⟩

theorem endFreeX_urnsPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7846⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endPackVatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endFreeUrnsCalldataMem I solcFreePtrMem).readWithPadding
            endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord ::
            endPackVatWord σ I :: ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I ::
            endFreeReturnPc :: sel :: [])
          (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd7847raw, hout⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endFreeUrnsWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
          endFreeUrnsOutPtr.toNat endFreeUrnsOutSize.toNat) = UInt256.ofNat 7 := by
      unfold endFreeUrnsOutPtr endFreeUrnsInSize endFreeUrnsOutSize
      decide +native
    simpa [endFreeUrnsPostCallMem, endFreeUrnsOutPtr, endFreeUrnsInSize,
      endFreeUrnsOutSize, endFreeUrnsEndPtr, hmin, haw] using rd7847raw

theorem endFreeX_urnsCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7846⟩
      (gasWord :: endPackVatWord σ I :: ⟨0⟩ :: endFreeUrnsOutPtr ::
        endFreeUrnsInSize :: endFreeUrnsOutPtr :: endFreeUrnsOutSize ::
        endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
      (⟨0⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsCalldataMem I solcFreePtrMem) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd7847raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeUrnsOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        endFreeUrnsOutPtr.toNat endFreeUrnsInSize.toNat)
        endFreeUrnsOutPtr.toNat endFreeUrnsOutSize.toNat) = UInt256.ofNat 7 := by
    unfold endFreeUrnsOutPtr endFreeUrnsInSize endFreeUrnsOutSize
    decide +native
  simpa [endFreeUrnsOutPtr, endFreeUrnsInSize, endFreeUrnsOutSize,
    endFreeUrnsEndPtr, hmin, byteArray_write_len_zero, haw] using rd7847raw

theorem endFreeX_urnsCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
      (⟨0⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨7847⟩) (okPc := ⟨7863⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_urnsCallSucceeded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
      (⟨1⟩ :: endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7865⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨7847⟩) (okPc := ⟨7863⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp)

theorem endFreeX_urnsReturnDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7865⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out acc k C)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7900⟩
      (endFreeUrnArtWord out :: endFreeUrnInkWord out :: endFreeIlkWord I ::
        endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out acc k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeUrnsPostCallMem I out).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeUrnsPostCallMem I out).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endFreeUrnsPostCallMem_size I out]; decide)
      (by decide) (endFreeUrnsPostCallMem_read64 I out)
  have hmload128 := endFreeUrnsPostCallMem_mload128 I out hlo
  have hmload160 := endFreeUrnsPostCallMem_mload160 I out hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd7900 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨7885⟩ (by decide +native) (by evm_ov)]
  have rdJump := rd7900
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd7900 := evm_run rdJump with [
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 (endFreeUrnInkWord out) (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mload 0 (endFreeUrnArtWord out) (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFreeUrnsEndPtr, endFreeUrnsSelectorWord, endFreeUrnsOutPtr,
      endFreeUrnsInSize, endFreeUrnsOutSize] using rd7900⟩

theorem endFreeX_urnsReturnDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7865⟩
      (endFreeUrnsEndPtr :: endFreeUrnsSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: ⟨0⟩ :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out acc k C)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeUrnsPostCallMem I out).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeUrnsPostCallMem I out).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endFreeUrnsPostCallMem_size I out]; decide)
      (by decide) (endFreeUrnsPostCallMem_read64 I out)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd7881 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨7885⟩ (by decide +native) (by evm_ov)]
  have rdShort := rd7881
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_artNonzero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel art ink : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hart : art ≠ ⟨0⟩)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7900⟩
      (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd7905 := evm_run h with [
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨7969⟩ (by decide +native) (by evm_ov)]
  have hzero : UInt256.isZero art = ⟨0⟩ := isZero_eq_zero_of_ne hart
  rw [hzero] at rd7905
  have rd7906 := rd7905.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd7906' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7906⟩
        (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
        mem (UInt256.ofNat 7) rdata acc (k + 1 + 1 + 1 + 1)
        (C + 3 + 3 + 3 + 10) := by
    convert rd7906 using 1
  exact endFree_solcErrorStringRevertTail_aw7
    (pc := ⟨7906⟩) (len := ⟨16⟩)
    (rawWord := ⟨0x456e642f6172742d6e6f742d7a65726f⟩) (shift := ⟨128⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6172742d6e6f742d7a65726f⟩ ⟨128⟩)
    (op := .PUSH16) (width := 16)
    rd7906'
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_artZero {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel ink : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7900⟩
      (⟨0⟩ :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7969⟩
      (⟨0⟩ :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k' C' := by
  have rd7969pre := evm_run h with [
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨7969⟩ (by decide +native) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd7969pre
  have rd7969 := rd7969pre.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa using rd7969⟩

theorem endFreeX_inkInRange {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel art ink : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hink : ink.toNat ≤ 2 ^ 255)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7969⟩
      (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8041⟩
      (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k' C' := by
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by decide +native
  have hgt : UInt256.gt ink endFreeInt256LimitWord = ⟨0⟩ := by
    apply ugt_zero
    rw [hlimit]
    exact hink
  have rd8041pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨255⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨8041⟩ (by decide +native) (by evm_ov)]
  rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8041pre
  have rd8041 := rd8041pre.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [endFreeInt256LimitWord] using rd8041⟩

theorem endFreeX_inkOverflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel art ink : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hink : 2 ^ 255 < ink.toNat)
    (hmem : mem.size = 196)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7969⟩
      (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata acc k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlimit : endFreeInt256LimitWord.toNat = 2 ^ 255 := by decide +native
  have hgt : UInt256.gt ink endFreeInt256LimitWord = ⟨1⟩ := by
    apply ugt_one
    rw [hlimit]
    exact hink
  have rd8041pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨255⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw gt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨8041⟩ (by decide +native) (by evm_ov)]
  rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8041pre
  have rd7982 := rd8041pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd7982' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7982⟩
        (art :: ink :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
        mem (UInt256.ofNat 7) rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10) := by
    convert rd7982 using 1
  exact endFree_solcErrorStringRevertTail_aw7
    (pc := ⟨7982⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd7982'
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_grabExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8041⟩
      (⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8143⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ ::
        endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
        endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σ' I :: ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I ::
        endFreeReturnPc :: sel :: [])
      (endFreeGrabCalldataMem σ' I out) (UInt256.ofNat 11) out (cA', σ') k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeUrnsPostCallMem I out).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeUrnsPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endFreeUrnsPostCallMem_size I out]; decide)
      (by decide) (endFreeUrnsPostCallMem_read64 I out)
  have hmload64Grab :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeGrabMem7 σ' I out).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeGrabMem7 σ' I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [endFreeGrabMem7_eq] using
      (mloadFreePtrValue
        (by rw [endFreeGrabCalldataMem_size σ' I out]; decide)
        (by decide) (endFreeGrabCalldataMem_read64 σ' I out))
  have hselectorShift :
      UInt256.shiftLeft (⟨0x01eeacfd⟩ : UInt256) ⟨230⟩ =
        endFreeGrabSelectorShifted := by
    decide +native
  have hsourceWord : EVM.word ↑I.source = solcSourceWord I := by
    change UInt256.ofNat I.source.val = solcSourceWord I
    rfl
  have hvowMask :
      UInt256.land (endSlotWord ⟨4⟩ σ' I) solcAddrMask = endPackVowWord σ' I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨4⟩ σ' I) = endPackVowWord σ' I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨4⟩ σ' I)
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σ' I) solcAddrMask = endPackVatWord σ' I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ' I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hdink :
      UInt256.sub ⟨0⟩ (endFreeUrnInkWord out) = endFreeGrabDinkWord out := by
    rfl
  have rd8044 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd8045raw⟩ := rd8044.sload (by decide +native) (by evm_ov)
  have rd8045 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8045⟩
        (endSlotWord ⟨1⟩ σ' I :: ⟨0⟩ :: endFreeUrnInkWord out ::
          endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
        (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd8045raw⟩
  obtain ⟨_, _, rd8045⟩ := rd8045
  have rd8048 := evm_run rd8045 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd8049raw⟩ := rd8048.sload (by decide +native) (by evm_ov)
  have rd8049 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8049⟩
        (endSlotWord ⟨4⟩ σ' I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σ' I ::
          ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc ::
          sel :: [])
        (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd8049raw⟩
  obtain ⟨_, _, rd8049⟩ := rd8049
  have rd8143raw := evm_run rd8049 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x01eeacfd⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨230⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endFreeGrabMem1 I out) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by rw [hselectorShift]; rfl) (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endFreeGrabMem2 I out) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endFreeGrabMem3 I out) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide +native]
        change (solcSourceWord I).toByteArray.write 0 (endFreeGrabMem2 I out) 164 32 =
          endFreeGrabMem3 I out
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeGrabMem4 I out) (UInt256.ofNat 8)
      (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide +native]
        change (solcSourceWord I).toByteArray.write 0 (endFreeGrabMem3 I out) 196 32 =
          endFreeGrabMem4 I out
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeGrabMem5 σ' I out) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨100⟩).toNat = 228 by decide +native]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨132⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeGrabMem6 σ' I out) (UInt256.ofNat 10)
      (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨132⟩).toNat = 260 by decide +native]
        rw [hdink]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨164⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 3 (endFreeGrabMem7 σ' I out) (UInt256.ofNat 11)
      (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨164⟩).toNat = 292 by decide +native]
        rfl)
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by decide +native)
      mem_cost hmload64Grab (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push4 ⟨0x7bab3f40⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨196⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have rd8143 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8143⟩
        (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ ::
          endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
          endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
          endPackVatWord σ' I :: ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I ::
          endFreeReturnPc :: sel :: [])
        (endFreeGrabMem7 σ' I out) (UInt256.ofNat 11) out (cA', σ') k' C' := by
    exact ⟨_, _, by
      simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
        endFreeGrabEndPtr, endFreeGrabSelectorWord, endPackVatWord, endPackVowWord,
        endSlotWord, solcSlotWord, solcAddrMask, hvatMask, hvatMaskLeft, hvowMask,
        hvowMaskLeft, haddrMask] using rd8143raw⟩
  obtain ⟨k', C', rd8143⟩ := rd8143
  exact ⟨k', C', by simpa [endFreeGrabMem7_eq] using rd8143⟩

theorem endFreeX_grabNoCode {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8041⟩
      (⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd8143⟩ := endFreeX_grabExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨8143⟩) (okPc := ⟨8155⟩) rd8143
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_grabCallReady {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8041⟩
      (⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeUrnsPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8158⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc ::
        sel :: [])
      (endFreeGrabCalldataMem σ' I out) (UInt256.ofNat 11) out (cA', σ') k' C' := by
  obtain ⟨_, _, rd8143⟩ := endFreeX_grabExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd8158⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨8143⟩) (okPc := ⟨8155⟩) rd8143
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd8158⟩

theorem endFreeX_grabPostCall {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8158⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc ::
        sel :: [])
      (endFreeGrabCalldataMem σ' I out) (UInt256.ofNat 11) out (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (endPackVatWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endFreeGrabCalldataMem σ' I out).readWithPadding
            endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
            endPackVatWord σ' I :: ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I ::
            endFreeReturnPc :: sel :: [])
          (endFreeGrabPostCallMem σ' I out ret) (UInt256.ofNat 11) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd8159raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endFreeGrabOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
      unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
      decide +native
    simpa [endFreeGrabPostCallMem, endFreeGrabOutPtr, endFreeGrabInSize,
      endFreeGrabOutSize, endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd8159raw

theorem endFreeX_grabCallDepthLimit {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8158⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc ::
        sel :: [])
      (endFreeGrabCalldataMem σ' I out) (UInt256.ofNat 11) out (cA', σ') k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeGrabCalldataMem σ' I out) (UInt256.ofNat 11)
      ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨k', C', rd8159raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
        endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
    unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
    decide +native
  simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
    endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw] using rd8159raw

theorem endFreeX_grabCallFailed {cA cA' gh bl σ σpre σpost σ₀ A I} {g : Sat256}
    {sel : UInt256} {out mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨8159⟩) (okPc := ⟨8175⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFreeX_grabCallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I} {g : Sat256}
    {sel : UInt256} {out mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
      (⟨1⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8177⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata (cA', σpost) k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨8159⟩) (okPc := ⟨8175⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp)

theorem endFreeX_grabLogReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σ : AccountMap} {out ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨8177⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σ I ::
        ⟨0⟩ :: endFreeUrnInkWord out :: endFreeIlkWord I :: endFreeReturnPc :: sel :: [])
      (endFreeGrabPostCallMem σ I out ret) (UInt256.ofNat 11) ret acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeGrabPostCallMem σ I out ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeGrabPostCallMem σ I out ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [endFreeGrabPostCallMem_eq]
    exact mloadFreePtrValue (by rw [endFreeGrabCalldataMem_size σ I out]; decide)
      (by decide) (endFreeGrabCalldataMem_read64 σ I out)
  have rd8184pre := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by decide +native) mem_cost hmload64
      (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rdLogMem := rd8184pre.mstore 0
    (endFreeLogDataMem σ I out ret) (UInt256.ofNat 11)
    (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥ (endFreeLogDataMem σ I out ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endFreeLogDataMem σ I out ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endFreeLogDataMem_size σ I out ret]; decide)
      (by decide) (endFreeLogDataMem_read64 σ I out ret)
  have rd8193 := evm_run rdLogMem with [
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by decide +native) mem_cost hmload64Log
      (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  have rdEvent := rd8193.pushConst
    (⟨0xf26f2b994a5e16f0960958e62541681f9e3e84d4caac2e487d25e0c75243f0d8⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide +native) (by decide +native) (by evm_ov)
  have rd8234pre := evm_run rdEvent with [
    raw swap2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd8234 : ∃ k' C', RD endBytecode I g s0 ⟨8234⟩
      [⟨128⟩, ⟨32⟩,
        ⟨0xf26f2b994a5e16f0960958e62541681f9e3e84d4caac2e487d25e0c75243f0d8⟩,
        endFreeIlkWord I, solcSourceWord I, ⟨0⟩, endFreeUrnInkWord out,
        endFreeIlkWord I, endFreeReturnPc, sel]
      (endFreeLogDataMem σ I out ret) (UInt256.ofNat 11) ret acc k' C' := by
    exact ⟨_, _, by simpa [solcSourceWord] using rd8234pre⟩
  obtain ⟨_, _, rd8234⟩ := rd8234
  have rdLog := RD.log3
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0xf26f2b994a5e16f0960958e62541681f9e3e84d4caac2e487d25e0c75243f0d8⟩)
    (d := endFreeIlkWord I) (e := solcSourceWord I)
    (t := [⟨0⟩, endFreeUrnInkWord out, endFreeIlkWord I, endFreeReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 11).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd8234 (by decide +native) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPop0 := RD.pop (a := (⟨0⟩ : UInt256))
    (t := [endFreeUrnInkWord out, endFreeIlkWord I, endFreeReturnPc, sel])
    rdLog (by decide +native) (by evm_ov)
  have rdPopInk := RD.pop (a := endFreeUrnInkWord out)
    (t := [endFreeIlkWord I, endFreeReturnPc, sel])
    rdPop0 (by decide +native) (by evm_ov)
  have rdPopIlk := RD.pop (a := endFreeIlkWord I)
    (t := [endFreeReturnPc, sel])
    rdPopInk (by decide +native) (by evm_ov)
  have rd562 := RD.jump (a := endFreeReturnPc) (t := [sel]) rdPopIlk
    (by decide +native) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endFreeReturnPc) (stk := [sel]) rd562
    (by decide +native) (by evm_ov)
  exact RD.stop rd563 (by decide +native) (by evm_ov)

theorem endDecode_free_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (freeTransition.params.map Param.name)
      (transitionSignature freeTransition).paramTypes I.calldata = some (endFreeStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = _
  simpa [config, endFreeStore, endFreeIlkValue, endFreeIlkWord, bytes32, bytes32Width,
    abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36

theorem endDecode_free_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (freeTransition.params.map Param.name)
      (transitionSignature freeTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk"] [bytes32] I.calldata = none
  simpa [config, bytes32, bytes32Width, abiBytes32, abiBytes32Width] using
    endDecode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk") hsz4 hshort

theorem endDispatchFree {I : ExecutionEnv}
    (hsel : selIs I (selectorOf freeTransition)) :
    dispatchMsg contract I.calldata = some freeTransition := by
  have hsel' : selIs I endFreeConcreteSelector := by
    simpa [endFreeConcreteSelector] using hsel
  have hcd : I.calldata.extract 0 4 = endFreeConcreteSelector :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some freeTransition
  unfold transitions
  simp [dispatchList, hcd, endFreeConcreteSelector, selectorBytes]
  decide +native

theorem endReachFreeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFreeConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFreeEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xc83062c6⟩ :=
    endSelWord_eq_of_beq I hsz 0xc8 0x30 0x62 0xc6 ⟨0xc83062c6⟩
      (by decide +native) (by simpa [selIs, endFreeConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup174FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup174FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup174FirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endFreeEntryPc 2 hfirst
    (fun j hj => endGroup174ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem endFreeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFreeEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFreeBodyPc
      [endFreeIlkWord I, endFreeReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := endFreeEntryPc) (ret := endFreeReturnPc)
    (decoded := endFreeDecodedPc) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz36 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcOneWordExternalJump
    (code := endBytecode) (decoded := endFreeDecodedPc) (ret := endFreeReturnPc)
    (routine := endFreeBodyPc) (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endFreeIlkWord, calldataWord] using hroutine⟩

theorem endFreeX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFreeEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel) (entry := endFreeEntryPc) (ret := endFreeReturnPc)
    (decoded := endFreeDecodedPc) (need := ⟨32⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem endFreeBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some freeTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endFreeEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endFreeX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_free_none_short hsz4 hshort)

private theorem endFree_accountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem endFree_accountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem endFree_callMade_accountMapEquiv_with_substate {cfg : Config}
    {evm_evm evm_solm : EVM.State}
    {tgt : EVM.Address} {targetWord : UInt256} {name : Ident} {args : List Value}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Substate}
    {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256} {callPerm : Bool}
    (hdepth : evm_evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
          evm_evm.genesisBlockHeader evm_evm.blocks evm_evm.accountMap evm_evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm_evm.executionEnv.codeOwner))
          evm_evm.executionEnv.sender (AccountAddress.ofUInt256 targetWord)
          (toExecute evm_evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name 0 args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) callPerm ∧
      accountMapEquiv σ' σ'_solm ∧ A' = A'_solm := by
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    endFree_accountMapExtensionalEq_of_accountMapEquiv hAccounts
  generalize htheta_solm :
    Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
      evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
      evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
      (toExecute evm_solm.accountMap tgt) callGas
      (UInt256.ofNat evm_solm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
      (mem.readWithPadding inOff.toNat inSize.toNat)
      (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
      callPerm = thetaRes
  have hcode_equiv :
      toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
    accountMapExtensionalEq_toExecute h_ext_eq tgt
  have htheta_solm' :
      Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes
        evm_evm.createdAccounts evm_evm.genesisBlockHeader evm_evm.blocks
        evm_solm.accountMap evm_evm.σ₀ A_in evm_evm.executionEnv.codeOwner
        evm_evm.executionEnv.sender tgt (toExecute evm_evm.accountMap tgt) callGas
        (UInt256.ofNat evm_evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
        (mem.readWithPadding inOff.toNat inSize.toNat)
        (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header callPerm =
        (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
          thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
    rw [← htheta_solm]
    rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
  let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
  have hΘ_evm := hΘ.symm
  rw [accountAddress_roundtrip, ← htgt] at hΘ_evm
  have hTheta_rel :=
    (accountMap_extensionality_of_Theta_and_Lambda
      (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
      (createdAccounts := evm_evm.createdAccounts)
      (genesisBlockHeader := evm_evm.genesisBlockHeader)
      (blocks := evm_evm.blocks)
      (σ₁ := evm_evm.accountMap)
      (σ₂ := evm_solm.accountMap)
      (σ₀ := evm_evm.σ₀)
      (A := A_in)
      (s := evm_evm.executionEnv.codeOwner)
      (o := evm_evm.executionEnv.sender)
      (r := tgt)
      (g := callGas)
      (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
      (v := (⟨0⟩ : UInt256))
      (v' := (⟨0⟩ : UInt256))
      (d := mem.readWithPadding inOff.toNat inSize.toNat)
      (i := ByteArray.empty)
      (ζ := none)
      (H := evm_evm.executionEnv.header)
      (w := callPerm)
      a1 a1
      (toExecute evm_evm.accountMap tgt)
      cA' thetaRes.1
      σ' thetaRes.2.1
      g'' thetaRes.2.2.1
      A' thetaRes.2.2.2.1
      z thetaRes.2.2.2.2.1
      out thetaRes.2.2.2.2.2
      (evm_evm.executionEnv.depth + 1)
      h_ext_eq).1 hΘ_evm htheta_solm'
  have hCreated' : cA' = thetaRes.1 := hTheta_rel.1
  have hTheta_s :
      (cA', thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1, z, out) =
        Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes
          evm_solm.createdAccounts evm_solm.genesisBlockHeader evm_solm.blocks
          evm_solm.accountMap evm_solm.σ₀ A_in evm_solm.executionEnv.codeOwner
          evm_solm.executionEnv.sender tgt (toExecute evm_solm.accountMap tgt)
          callGas (UInt256.ofNat evm_solm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header callPerm := by
    rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
    rw [hCreated']
    exact htheta_solm.symm
  refine ⟨thetaRes.2.1, thetaRes.2.2.2.1, ?_, ?_, ?_⟩
  · refine ⟨mem.readWithPadding inOff.toNat inSize.toNat, hcd, ?_⟩
    exact callViaEVM.callMade (perm := callPerm) wordOfInt_zero.symm
      ⟨callGas, A_in, hTheta_s⟩ rfl
      (by
        rw [hEnv]
        rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
        show (0 : Nat) ≤
          ((evm_evm.accountMap.find? evm_evm.executionEnv.codeOwner).elim ⟨0⟩
            (fun x => x.balance)).toNat
        exact Nat.zero_le _)
      (by
        rw [hEnv]
        exact hdepth)
  · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 :=
      hTheta_rel.2.2.2.2.2
    exact endFree_accountMapEquiv_of_accountMapExtensionalEq hσext
  · exact hTheta_rel.2.2.1

theorem endFreeBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf freeTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFreeConcreteSelector := by
    simpa [endFreeConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFreeConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some freeTransition :=
    endDispatchFree hsel
  have hreach := endReachFreeBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_free_ok (I := I) hsz36
    obtain ⟨_, _, hbodyReach⟩ :=
      endFreeX_decoded (g := Sat256.ofUInt256 g) hsz36 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hliveCouple :
        endSlotWord ⟨8⟩ σ_evm I = endSlotWord ⟨8⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hlive : endSlotWord ⟨8⟩ σ_evm I = ⟨0⟩
    · obtain ⟨_, _, hlivePc⟩ := endFreeX_liveZero (I := I) hlive hbodyReach
      have hliveSolm : endSlotWord ⟨8⟩ σ_solm I = ⟨0⟩ := by
        rw [← hliveCouple]
        exact hlive
      have hAddressId (a : AccountAddress) : EVM.address a = a := by
        apply Fin.ext
        show ↑a % EVM.twoPow 160 = ↑a
        rw [Nat.mod_eq_of_lt]
        exact a.isLt
      by_cases hvatCode :
          Reasoning.Theory.extCodeSizeWord σ_evm (endPackVatWord σ_evm I) =
            ⟨0⟩
      · have hvatCodeSolm :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endPackVatWord σ_solm I) = ⟨0⟩ :=
          endPackVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
        have hbody :
            ExecTransitionBody config contract evmSolm (endFreeStore I)
              freeTransition.body .reverted := by
          simpa [evmSolm] using
            endFreeBodyReverts_urnsNoCode
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hliveSolm hvatCodeSolm
        exact (endFreeX_urnsNoCode (g := Sat256.ofUInt256 g) hlivePc hvatCode)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatCodeNE :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (endPackVatWord σ_evm I) ≠ ⟨0⟩ := hvatCode
        have hvatCodeSolmNE :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endPackVatWord σ_solm I) ≠ ⟨0⟩ :=
          endPackVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeNE
        obtain ⟨gasWord, _, _, hcallReady⟩ :=
          endFreeX_urnsCallReady (g := Sat256.ofUInt256 g) hlivePc hvatCodeNE
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA', σ', z, out, Ain, callGas, _, _, hΘ, rd7847, hout⟩ :=
            endFreeX_urnsPostCall hcallReady hdepthLt
          rcases hΘ with ⟨g'', A', hΘeq⟩
          have hdepthNe :
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
                1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [initState] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          have htgt :
              EVM.address (endPackVatAddr σ_evm I) =
                AccountAddress.ofUInt256 (endPackVatWord σ_evm I) := by
            calc
              EVM.address (endPackVatAddr σ_evm I)
                  = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ_evm I)) := by
                    rw [endPackVatAddr_eq_ofUInt256]
              _ = AccountAddress.ofUInt256 (endPackVatWord σ_evm I) :=
                    hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_evm I))
          obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, hAccountsUrns, hSubstateUrns⟩ :=
            endFree_callMade_accountMapEquiv_with_substate
              (cfg := config)
              (evm_evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (evm_solm := evmSolm)
              (tgt := EVM.address (endPackVatAddr σ_evm I))
              (targetWord := endPackVatWord σ_evm I)
              (name := "urns")
              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source])
              (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
              (z := z) (out := out) (g'' := g'') (callGas := callGas)
              (mem := endFreeUrnsCalldataMem I solcFreePtrMem)
              (inOff := endFreeUrnsOutPtr) (inSize := endFreeUrnsInSize)
              (callPerm := true)
              hdepthNe htgt (endFreeUrnsEncode_eq I hsz36 solcFreePtrMem_size)
              (by simpa [initState, hperm] using hΘeq)
              hAccounts
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
          have hVatAddr : endPackVatAddr σ_evm I = endPackVatAddr σ_solm I := by
            simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccounts]
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endPackVatAddr σ_solm I)) "urns" 0
                [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
                (z,
                  { evmSolm with
                    accountMap := σ'_solm
                    substate := A'_solm
                    createdAccounts := cA' },
                  out) true := by
            simpa [hVatAddr] using hcallSolmRaw
          cases z
          · have hbody :
                ExecTransitionBody config contract evmSolm (endFreeStore I)
                  freeTransition.body .reverted := by
              simpa [evmSolm] using
                endFreeBodyReverts_urnsCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmUrns :=
                    { evmSolm with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' })
                  (out := out)
                  hwv hliveSolm hvatCodeSolmNE (by simpa [evmSolm] using hcallSolm)
            exact (endFreeX_urnsCallFailed (g := Sat256.ofUInt256 g) rd7847 hout)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · let evmUrnsEvm :=
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σ'
                substate := A'
                createdAccounts := cA' }
            let evmUrnsSolm :=
              { evmSolm with
                accountMap := σ'_solm
                substate := A'_solm
                createdAccounts := cA' }
            have hStateCall : EVMStateEquiv evmUrnsEvm evmUrnsSolm := by
              refine ⟨?_, ?_, ?_⟩
              · simp [evmUrnsEvm, evmUrnsSolm, evmSolm, initState]
              · simp [evmUrnsEvm, evmUrnsSolm]
              · simpa [evmUrnsEvm, evmUrnsSolm] using hAccountsUrns
            have hSubstateCall : evmUrnsSolm.substate = evmUrnsEvm.substate := by
              simpa [evmUrnsEvm, evmUrnsSolm] using hSubstateUrns.symm
            have hsrcUrns : evmUrnsSolm.executionEnv.source = I.source := by
              simp [evmUrnsSolm, evmSolm, initState]
            have hownerUrns : evmUrnsSolm.executionEnv.codeOwner = I.codeOwner := by
              simp [evmUrnsSolm, evmSolm, initState]
            obtain ⟨_, _, rd7865⟩ := endFreeX_urnsCallSucceeded rd7847
            by_cases hshort : out.size < 64
            · have hbody :
                  ExecTransitionBody config contract evmSolm (endFreeStore I)
                    freeTransition.body .reverted := by
                simpa [evmSolm, evmUrnsSolm] using
                  endFreeBodyReverts_urnsDecodeShort
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmUrns := evmUrnsSolm)
                    (out := out)
                    hwv hliveSolm hvatCodeSolmNE
                    (by simpa [evmSolm, evmUrnsSolm] using hcallSolm) hshort
              exact (endFreeX_urnsReturnDecodeShort rd7865 hshort hout)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hlo : 64 ≤ out.size := by omega
              obtain ⟨_, _, rd7900⟩ := endFreeX_urnsReturnDecodeOk rd7865 hlo hout
              by_cases hartNonzero : endFreeUrnArtWord out ≠ ⟨0⟩
              · have hbody :
                    ExecTransitionBody config contract evmSolm (endFreeStore I)
                      freeTransition.body .reverted := by
                  simpa [evmSolm, evmUrnsSolm] using
                    endFreeBodyReverts_artNonzero
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := g) (evmUrns := evmUrnsSolm)
                      (out := out)
                      hwv hliveSolm hvatCodeSolmNE
                      (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                      hlo hartNonzero
                exact (endFreeX_artNonzero hartNonzero
                    (endFreeUrnsPostCallMem_size I out)
                    (endFreeUrnsPostCallMem_read64 I out) rd7900)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hartZero : endFreeUrnArtWord out = ⟨0⟩ := by
                  by_contra hbad
                  exact hartNonzero hbad
                have rd7900zero := rd7900
                rw [hartZero] at rd7900zero
                obtain ⟨_, _, rd7969⟩ := endFreeX_artZero rd7900zero
                by_cases hinkOverflow : 2 ^ 255 < (endFreeUrnInkWord out).toNat
                · have hbody :
                      ExecTransitionBody config contract evmSolm (endFreeStore I)
                        freeTransition.body .reverted := by
                    simpa [evmSolm, evmUrnsSolm] using
                      endFreeBodyReverts_inkOverflow
                        (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                        (A := A) (I := I) (g := g) (evmUrns := evmUrnsSolm)
                        (out := out)
                        hwv hliveSolm hvatCodeSolmNE
                        (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                        hlo hartZero hinkOverflow
                  exact (endFreeX_inkOverflow hinkOverflow
                      (endFreeUrnsPostCallMem_size I out)
                      (endFreeUrnsPostCallMem_read64 I out) rd7969)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hinkOk : (endFreeUrnInkWord out).toNat ≤ 2 ^ 255 := by omega
                  obtain ⟨_, _, rd8041⟩ := endFreeX_inkInRange hinkOk rd7969
                  by_cases hgrabCode :
                      Reasoning.Theory.extCodeSizeWord σ'
                        (endPackVatWord σ' I) = ⟨0⟩
                  · have hgrabCodeSolm :
                        Reasoning.Theory.extCodeSizeWord evmUrnsSolm.accountMap
                          (endPackVatWord evmUrnsSolm.accountMap I) = ⟨0⟩ := by
                      simpa [evmUrnsEvm, evmUrnsSolm] using
                        endPackVatCodeSize_zero_accountMapEquiv hStateCall.accountMap
                          hgrabCode
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endFreeStore I)
                          freeTransition.body .reverted := by
                      simpa [evmSolm, evmUrnsSolm] using
                        endFreeBodyReverts_grabNoCode
                          (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                          (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          (evmUrns := evmUrnsSolm) (out := out)
                          hwv hliveSolm hvatCodeSolmNE
                          (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                          hlo hownerUrns hartZero hinkOk hgrabCodeSolm
                    exact (endFreeX_grabNoCode rd8041 hgrabCode)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hgrabCodeNE :
                        Reasoning.Theory.extCodeSizeWord σ'
                          (endPackVatWord σ' I) ≠ ⟨0⟩ := hgrabCode
                    have hgrabCodeSolmNE :
                        Reasoning.Theory.extCodeSizeWord evmUrnsSolm.accountMap
                          (endPackVatWord evmUrnsSolm.accountMap I) ≠ ⟨0⟩ := by
                      simpa [evmUrnsEvm, evmUrnsSolm] using
                        endPackVatCodeSize_ne_accountMapEquiv hStateCall.accountMap
                          hgrabCodeNE
                    obtain ⟨grabGasWord, _, _, rdGrabReady⟩ :=
                      endFreeX_grabCallReady rd8041 hgrabCodeNE
                    by_cases hgrabDepthLt : I.depth.val < 1024
                    · obtain ⟨cA'', σ'', zGrab, ret, AinGrab, callGasGrab, _, _, hΘGrab,
                          rd8159, hretSize⟩ :=
                        endFreeX_grabPostCall rdGrabReady hgrabDepthLt
                      rcases hΘGrab with ⟨gGrab'', AGrab', hΘGrabEq⟩
                      have hdepthNeGrab : evmUrnsEvm.executionEnv.depth ≠ 1024 := by
                        intro hbad
                        have hbadI : I.depth = 1024 := by
                          simpa [evmUrnsEvm, initState] using hbad
                        have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
                        omega
                      have htgtGrab :
                          EVM.address (endPackVatAddr σ' I) =
                            AccountAddress.ofUInt256 (endPackVatWord σ' I) := by
                        calc
                          EVM.address (endPackVatAddr σ' I)
                              = EVM.address (AccountAddress.ofUInt256 (endPackVatWord σ' I)) := by
                                rw [endPackVatAddr_eq_ofUInt256]
                          _ = AccountAddress.ofUInt256 (endPackVatWord σ' I) :=
                                hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ' I))
                      obtain ⟨σ''_solm, A''_solm, hgrabCallSolmRaw, hAccountsGrab,
                          hSubstateGrab⟩ :=
                        endFree_callMade_accountMapEquiv_with_substate
                          (cfg := config) (evm_evm := evmUrnsEvm)
                          (evm_solm := evmUrnsSolm)
                          (tgt := EVM.address (endPackVatAddr σ' I))
                          (targetWord := endPackVatWord σ' I)
                          (name := "grab")
                          (args :=
                            [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                              .address I.source,
                              .address I.source,
                              .address (endPackVowAddr σ' I),
                              .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
                              .int 0])
                          (cA' := cA'') (σ' := σ'') (A' := AGrab')
                          (A_in := AinGrab) (z := zGrab) (out := ret)
                          (g'' := gGrab'') (callGas := callGasGrab)
                          (mem := endFreeGrabCalldataMem σ' I out)
                          (inOff := endFreeGrabOutPtr) (inSize := endFreeGrabInSize)
                          (callPerm := true)
                          hdepthNeGrab htgtGrab
                          (endFreeGrabEncode_eq σ' I out hsz36 hinkOk)
                          (by simpa [evmUrnsEvm, initState, hperm] using hΘGrabEq)
                          hStateCall.accountMap
                          (by simp [evmUrnsEvm, evmUrnsSolm, evmSolm, initState])
                          (by simp [evmUrnsEvm, evmUrnsSolm])
                          (by simp [evmUrnsEvm, evmUrnsSolm, evmSolm, initState])
                          (by simp [evmUrnsEvm, evmUrnsSolm, evmSolm, initState])
                          (by simpa [evmUrnsEvm, evmUrnsSolm] using hStateCall.executionEnv.symm)
                      have hVatWordGrab :
                          endPackVatWord σ' I = endPackVatWord evmUrnsSolm.accountMap I := by
                        simpa [evmUrnsEvm, evmUrnsSolm] using
                          endPackVatWord_accountMapEquiv hStateCall.accountMap
                      have hVatAddrGrab :
                          endPackVatAddr σ' I = endPackVatAddr evmUrnsSolm.accountMap I := by
                        simp [endPackVatAddr, hVatWordGrab]
                      have hVowWordGrab :
                          endPackVowWord σ' I = endPackVowWord evmUrnsSolm.accountMap I := by
                        have hslot :
                            endSlotWord ⟨4⟩ σ' I =
                              endSlotWord ⟨4⟩ evmUrnsSolm.accountMap I := by
                          simpa [evmUrnsEvm, evmUrnsSolm, endSlotWord, solcSlotWord] using
                            accountMapEquiv_storage_findD hStateCall.accountMap
                              I.codeOwner ⟨4⟩ ⟨0⟩
                        simpa [endPackVowWord] using
                          congrArg (fun w => UInt256.land w solcAddrMask) hslot
                      have hVowAddrGrab :
                          endPackVowAddr σ' I = endPackVowAddr evmUrnsSolm.accountMap I := by
                        simp [endPackVowAddr, hVowWordGrab]
                      have hgrabCallSolm :
                          typedCallViaEVM config evmUrnsSolm
                            (EVM.address (endPackVatAddr evmUrnsSolm.accountMap I)) "grab" 0
                            [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                              .address I.source,
                              .address I.source,
                              .address (endPackVowAddr evmUrnsSolm.accountMap I),
                              .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
                              .int 0]
                            (zGrab,
                              { evmUrnsSolm with
                                accountMap := σ''_solm
                                substate := A''_solm
                                createdAccounts := cA'' },
                              ret) true := by
                        simpa [hVatAddrGrab, hVowAddrGrab] using hgrabCallSolmRaw
                      cases zGrab
                      · have hbody :
                            ExecTransitionBody config contract evmSolm (endFreeStore I)
                              freeTransition.body .reverted := by
                          simpa [evmSolm, evmUrnsSolm] using
                            endFreeBodyReverts_grabCallFailed
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmUrns := evmUrnsSolm)
                              (evmGrab :=
                                { evmUrnsSolm with
                                  accountMap := σ''_solm
                                  substate := A''_solm
                                  createdAccounts := cA'' })
                              (out := out) (grabOut := ret)
                              hwv hliveSolm hvatCodeSolmNE
                              (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                              hlo hsrcUrns hownerUrns hartZero hinkOk hgrabCodeSolmNE
                              (by simpa [evmUrnsSolm] using hgrabCallSolm)
                        have rd8159Fail := rd8159
                        simp at rd8159Fail
                        exact (endFreeX_grabCallFailed rd8159Fail hretSize)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · let evmGrabEvm :=
                          { evmUrnsEvm with
                            accountMap := σ''
                            substate := AGrab'
                            createdAccounts := cA'' }
                        let evmGrabSolm :=
                          { evmUrnsSolm with
                            accountMap := σ''_solm
                            substate := A''_solm
                            createdAccounts := cA'' }
                        have hStateGrab : EVMStateEquiv evmGrabEvm evmGrabSolm := by
                          refine ⟨?_, ?_, ?_⟩
                          · simpa [evmGrabEvm, evmGrabSolm] using hStateCall.executionEnv
                          · simp [evmGrabEvm, evmGrabSolm]
                          · simpa [evmGrabEvm, evmGrabSolm] using hAccountsGrab
                        have rd8159Succ := rd8159
                        simp at rd8159Succ
                        obtain ⟨_, _, rd8177⟩ := endFreeX_grabCallSucceeded rd8159Succ
                        have hretEvm := endFreeX_grabLogReturn
                          (σ := σ') (out := out) (ret := ret) hperm rd8177
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endFreeStore I)
                              freeTransition.body
                              (.returned { contract := contract, locals := endFreeStoreGrab I out }
                                evmGrabSolm none) := by
                          simpa [evmSolm, evmUrnsSolm, evmGrabSolm] using
                            endFreeBodyReturns_grabSuccess
                              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                              (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (evmUrns := evmUrnsSolm) (evmGrab := evmGrabSolm)
                              (out := out) (grabOut := ret)
                              hwv hliveSolm hvatCodeSolmNE
                              (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                              hlo hsrcUrns hownerUrns hartZero hinkOk hgrabCodeSolmNE
                              (by simpa [evmUrnsSolm, evmGrabSolm] using hgrabCallSolm)
                        exact hretEvm.reEquivExecutionGenEVMStateEquiv
                          (evm'_evm := evmGrabEvm) (evm'_solm := evmGrabSolm)
                          hcode hdispatch hdecode hbody
                          (by simp [evmGrabEvm])
                          (by
                            simpa [evmGrabEvm] using accountMapEquiv.refl σ'')
                          hStateGrab
                          (by
                            simpa [freeTransition] using
                              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none)
                                (t := []) (dvs := []) rfl (by decide +native)
                                (by decide +native)))
                    · rw [not_lt] at hgrabDepthLt
                      have hgrabDepthEq : I.depth = 1024 :=
                        Fin.ext (by have := I.depth.isLt; omega)
                      obtain ⟨_, _, rd8159⟩ :=
                        endFreeX_grabCallDepthLimit rdGrabReady hgrabDepthEq
                      let A_grab :=
                        (evmUrnsSolm.addAccessedAccount
                          (EVM.address (endPackVatAddr evmUrnsSolm.accountMap I))).substate
                      have hgrabCallSolm :
                          typedCallViaEVM config evmUrnsSolm
                            (EVM.address (endPackVatAddr evmUrnsSolm.accountMap I)) "grab" 0
                            [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                              .address I.source,
                              .address I.source,
                              .address (endPackVowAddr evmUrnsSolm.accountMap I),
                              .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
                              .int 0]
                            (false, { evmUrnsSolm with substate := A_grab },
                              ByteArray.empty) true := by
                        simpa [A_grab] using
                          (callNotMade_depthLimit (cfg := config) (evm := evmUrnsSolm)
                            (tgt := EVM.address (endPackVatAddr evmUrnsSolm.accountMap I))
                            (name := "grab")
                            (args :=
                              [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                .address I.source,
                                .address I.source,
                                .address (endPackVowAddr evmUrnsSolm.accountMap I),
                                .int (-(Int.ofNat (endFreeUrnInkWord out).toNat)),
                                .int 0])
                            (callPerm := true)
                            (endFreeGrabEncode_eq evmUrnsSolm.accountMap I out hsz36 hinkOk)
                            (by simpa [evmUrnsSolm, evmSolm, initState] using hgrabDepthEq))
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endFreeStore I)
                            freeTransition.body .reverted := by
                        simpa [evmSolm, evmUrnsSolm] using
                          endFreeBodyReverts_grabCallFailed
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            (evmUrns := evmUrnsSolm)
                            (evmGrab := { evmUrnsSolm with substate := A_grab })
                            (out := out) (grabOut := ByteArray.empty)
                            hwv hliveSolm hvatCodeSolmNE
                            (by simpa [evmSolm, evmUrnsSolm] using hcallSolm)
                            hlo hsrcUrns hownerUrns hartZero hinkOk hgrabCodeSolmNE
                            (by simpa [evmUrnsSolm] using hgrabCallSolm)
                      exact (endFreeX_grabCallFailed rd8159 (by decide +native))
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rd7847⟩ :=
            endFreeX_urnsCallDepthLimit (g := Sat256.ofUInt256 g) hcallReady hdepthEq
          let A_urns :=
            (evmSolm.addAccessedAccount (EVM.address (endPackVatAddr σ_solm I))).substate
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endPackVatAddr σ_solm I)) "urns" 0
                [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source]
                (false, { evmSolm with substate := A_urns }, ByteArray.empty) true := by
            simpa [evmSolm, A_urns] using
              (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                (tgt := EVM.address (endPackVatAddr σ_solm I)) (name := "urns")
                (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I), .address I.source])
                (callPerm := true)
                (endFreeUrnsEncode_eq I hsz36 solcFreePtrMem_size)
                (by simpa [evmSolm, initState] using hdepthEq))
          have hbody :
              ExecTransitionBody config contract evmSolm (endFreeStore I)
                freeTransition.body .reverted := by
            simpa [evmSolm] using
              endFreeBodyReverts_urnsCallFailed
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                (evmUrns := { evmSolm with substate := A_urns })
                (out := ByteArray.empty)
                hwv hliveSolm hvatCodeSolmNE (by simpa [evmSolm] using hcallSolm)
          exact (endFreeX_urnsCallFailed (g := Sat256.ofUInt256 g) rd7847
              (by decide +native))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact hlive (by rw [hliveCouple, hbad])
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endFreeStore I) freeTransition.body .reverted := by
        simpa using
          endFreeSourceLiveReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hliveSolm
      exact (endFreeX_liveNonzero (I := I) (g := Sat256.ofUInt256 g) hlive hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endFreeBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
