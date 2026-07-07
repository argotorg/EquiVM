import Benchmarks.EAS.Attester.OuterArrayInit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! Helpers for the nested dynamic arrays used by `multiAttest` and `multiRevoke`. -/

abbrev attesterSecondArrayPayloadStartWord (I : ExecutionEnv) : UInt256 :=
  (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩

abbrev attesterFirstInnerArrayOffsetWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (attesterSecondArrayPayloadStartWord I).toNat

abbrev attesterFirstInnerArrayStartWord (I : ExecutionEnv) : UInt256 :=
  attesterSecondArrayPayloadStartWord I + attesterFirstInnerArrayOffsetWord I

abbrev attesterFirstInnerArrayLengthWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (attesterFirstInnerArrayStartWord I).toNat

abbrev attesterFirstInnerArrayPayloadStartWord (I : ExecutionEnv) : UInt256 :=
  attesterFirstInnerArrayStartWord I + ⟨32⟩

abbrev attesterFirstInnerArrayPayloadEndWord (I : ExecutionEnv) : UInt256 :=
  attesterFirstInnerArrayPayloadStartWord I +
    UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩

theorem attesterSecondArrayPayloadStart_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    (attesterSecondArrayPayloadStartWord I).toNat =
      4 + (calldataWord I.calldata 36).toNat + 32 := by
  unfold attesterSecondArrayPayloadStartWord
  rw [uadd_toNat]
  rw [attesterSecondArrayStart_toNat (I := I) hoffMax]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
    omega)

theorem readNat_drop4_at_some_size {cd : ByteArray} {off n : Nat}
    (hread : readNat? (cd.toList.drop 4) off = some n) :
    4 + off + 32 ≤ cd.size := by
  unfold readNat? readWord? readBytes? at hread
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  by_cases hlen : 32 ≤ cd.toList.length - (4 + off)
  · rw [htlen] at hlen
    omega
  · simp [hlen] at hread

theorem readNat_drop4_at_some_eq_calldataWord {cd : ByteArray} {off n : Nat}
    (hread : readNat? (cd.toList.drop 4) off = some n) :
    n = (calldataWord cd (4 + off)).toNat := by
  have hsize := readNat_drop4_at_some_size (cd := cd) (off := off) (n := n) hread
  have hword := readNat_drop4_at_eq_calldataWord (cd := cd) (off := off) hsize
  rw [hword] at hread
  cases hread
  rfl

private theorem attester_slt_one_low {a b : UInt256}
    (hlt : a.toNat < b.toNat) (hb : b.toNat < 2 ^ 255) :
    UInt256.slt a b = ⟨1⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255),
      if_neg (by omega : ¬ b.toNat ≥ 2 ^ 255)]
  rw [decide_eq_true (show a < b by
    show a.toNat < b.toNat
    exact hlt)]
  native_decide

private theorem attester_sgt_zero_low {a b : UInt256}
    (hle : a.toNat ≤ b.toNat) (hb : b.toNat < 2 ^ 255) :
    UInt256.sgt a b = ⟨0⟩ := by
  unfold UInt256.sgt UInt256.sgtBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255),
      if_neg (by omega : ¬ b.toNat ≥ 2 ^ 255)]
  rw [decide_eq_false (show ¬ a > b by
    show ¬ a.toNat > b.toNat
    omega)]
  native_decide

set_option maxHeartbeats 1000000 in
theorem attesterFirstInnerArrayGuardFacts_of_decode {I : ExecutionEnv}
    {elem : ElemType} {relativeOffset : Nat} {inner : List Value} {innerEnd : Nat}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hreadFirst : readNat? (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32) = some relativeOffset)
    (hinner : decodeABIValue? (.dynamicArray (.elem elem)) (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
      some (.array inner, innerEnd))
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    UInt256.slt (attesterFirstInnerArrayOffsetWord I)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ ∧
    UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ ∧
    UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩ := by
  obtain ⟨innerLen, hreadLen, hlenMax, hend, hendLe, _hlenValues⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hinner
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hsizeSigned
  have hdropLen : (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
  have hbaseToNat :
      (attesterSecondArrayPayloadStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 :=
    attesterSecondArrayPayloadStart_toNat (I := I) hoffMax
  have hoffWordToNat :
      (attesterFirstInnerArrayOffsetWord I).toNat = relativeOffset := by
    unfold attesterFirstInnerArrayOffsetWord
    rw [hbaseToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadFirst
    simpa [Nat.add_assoc] using hreadEq.symm
  have hinnerLenReadSizeEarly := readNat?_some_length hreadLen
  have hinnerHeadInCalldataEarly :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) + 32 ≤
        I.calldata.size := by
    rw [hdropLen] at hinnerLenReadSizeEarly
    omega
  have hstartToNat :
      (attesterFirstInnerArrayStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset := by
    unfold attesterFirstInnerArrayStartWord
    rw [uadd_toNat, hbaseToNat, hoffWordToNat]
    exact Nat.mod_eq_of_lt (by
      omega)
  have hlenWordToNat :
      (attesterFirstInnerArrayLengthWord I).toNat = innerLen := by
    unfold attesterFirstInnerArrayLengthWord
    rw [hstartToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadLen
    simpa [Nat.add_assoc] using hreadEq.symm
  have hinnerLenWordOk :
      UInt256.gt (attesterFirstInnerArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hlenWordToNat, hmaxToNat]
    exact Nat.le_of_not_gt hlenMax
  have hinnerHeadInCalldata :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) + 32 ≤
        I.calldata.size := hinnerHeadInCalldataEarly
  have hpayloadInCalldata :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 +
          32 * innerLen) ≤ I.calldata.size := by
    rw [hend] at hendLe
    rw [hdropLen] at hendLe
    omega
  have hsubHeadToNat :
      (UInt256.sub (UInt256.ofNat I.calldata.size)
          (attesterSecondArrayPayloadStartWord I)).toNat =
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) := by
    rw [usub_toNat]
    · rw [ulit_toNat' I.calldata.size hsize, hbaseToNat]
    · rw [ulit_toNat' I.calldata.size hsize, hbaseToNat]
      omega
  have hrhsOffsetToNat :
      (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (attesterSecondArrayPayloadStartWord I))
          (UInt256.lnot (⟨30⟩ : UInt256))).toNat =
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31 := by
    change ((UInt256.sub (UInt256.ofNat I.calldata.size)
        (attesterSecondArrayPayloadStartWord I) + UInt256.lnot (⟨30⟩ : UInt256)).toNat =
      I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31)
    rw [uadd_toNat, hsubHeadToNat]
    have hlnot : (UInt256.lnot (⟨30⟩ : UInt256)).toNat = UInt256.size - 31 := by
      native_decide
    rw [hlnot]
    have hsplit :
        I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) +
            (UInt256.size - 31) =
          UInt256.size +
            (I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31) := by
      omega
    rw [hsplit, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by
      have hleSub :
          I.calldata.size - (4 + (calldataWord I.calldata 36).toNat + 32) - 31 ≤
            I.calldata.size := by
        omega
      exact lt_of_le_of_lt hleSub hsize)
  have hoffsetGuard :
      UInt256.slt (attesterFirstInnerArrayOffsetWord I)
          (UInt256.add
            (UInt256.sub (UInt256.ofNat I.calldata.size)
              (attesterSecondArrayPayloadStartWord I))
            (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩ := by
    apply attester_slt_one_low
    · rw [hoffWordToNat, hrhsOffsetToNat]
      omega
    · rw [hrhsOffsetToNat]
      omega
  have hinnerPayloadStartToNat :
      (attesterFirstInnerArrayStartWord I + ⟨32⟩).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset + 32 := by
    rw [uadd_toNat, hstartToNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    exact Nat.mod_eq_of_lt (by
      omega)
  have hshiftLenToNat :
      (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩).toNat =
        32 * innerLen := by
    have hle : (attesterFirstInnerArrayLengthWord I).toNat ≤ solcMaxU64 := by
      rw [hlenWordToNat]
      exact Nat.le_of_not_gt hlenMax
    simpa [hlenWordToNat] using
      attesterShiftLeft5_toNat_of_le (attesterFirstInnerArrayLengthWord I) hle
  have hsubPayloadToNat :
      (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)).toNat =
        I.calldata.size - 32 * innerLen := by
    rw [usub_toNat]
    · rw [ulit_toNat' I.calldata.size hsize, hshiftLenToNat]
    · rw [ulit_toNat' I.calldata.size hsize, hshiftLenToNat]
      omega
  have hpayloadGuard :
      UInt256.sgt (attesterFirstInnerArrayStartWord I + ⟨32⟩)
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (UInt256.shiftLeft (attesterFirstInnerArrayLengthWord I) ⟨5⟩)) = ⟨0⟩ := by
    apply attester_sgt_zero_low
    · rw [hinnerPayloadStartToNat, hsubPayloadToNat]
      omega
    · rw [hsubPayloadToNat]
      omega
  exact ⟨hoffsetGuard, hinnerLenWordOk, hpayloadGuard⟩

theorem attesterFirstInnerArrayLengthWord_toNat_of_decode {I : ExecutionEnv}
    {elem : ElemType} {relativeOffset : Nat} {inner : List Value} {innerEnd : Nat}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hreadFirst : readNat? (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32) = some relativeOffset)
    (hinner : decodeABIValue? (.dynamicArray (.elem elem)) (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
      some (.array inner, innerEnd))
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    (attesterFirstInnerArrayLengthWord I).toNat = inner.length := by
  obtain ⟨innerLen, hreadLen, _hlenMax, _hend, _hendLe, hlenValues⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hinner
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt_sign hsizeSigned
  have hdropLen : (I.calldata.toList.drop 4).length = I.calldata.size - 4 := by
    rw [List.length_drop]
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
  have hbaseToNat :
      (attesterSecondArrayPayloadStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 :=
    attesterSecondArrayPayloadStart_toNat (I := I) hoffMax
  have hoffWordToNat :
      (attesterFirstInnerArrayOffsetWord I).toNat = relativeOffset := by
    unfold attesterFirstInnerArrayOffsetWord
    rw [hbaseToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadFirst
    simpa [Nat.add_assoc] using hreadEq.symm
  have hinnerLenReadSize := readNat?_some_length hreadLen
  have hinnerHeadInCalldata :
      4 + ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) + 32 ≤
        I.calldata.size := by
    rw [hdropLen] at hinnerLenReadSize
    omega
  have hstartToNat :
      (attesterFirstInnerArrayStartWord I).toNat =
        4 + (calldataWord I.calldata 36).toNat + 32 + relativeOffset := by
    unfold attesterFirstInnerArrayStartWord
    rw [uadd_toNat, hbaseToNat, hoffWordToNat]
    exact Nat.mod_eq_of_lt (by
      omega)
  have hword :
      (attesterFirstInnerArrayLengthWord I).toNat = innerLen := by
    unfold attesterFirstInnerArrayLengthWord
    rw [hstartToNat]
    have hreadEq :=
      readNat_drop4_at_some_eq_calldataWord (cd := I.calldata) hreadLen
    simpa [Nat.add_assoc] using hreadEq.symm
  rw [hword, hlenValues]

theorem attesterFirstInnerArrayLengthWord_le_solcMaxU64_of_decode {I : ExecutionEnv}
    {elem : ElemType} {relativeOffset : Nat} {inner : List Value} {innerEnd : Nat}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hreadFirst : readNat? (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32) = some relativeOffset)
    (hinner : decodeABIValue? (.dynamicArray (.elem elem)) (I.calldata.toList.drop 4)
        ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
      some (.array inner, innerEnd))
    (hsizeSigned : I.calldata.size < 2 ^ 255) :
    (attesterFirstInnerArrayLengthWord I).toNat ≤ solcMaxU64 := by
  obtain ⟨_innerLen, _hreadLen, hlenMax, _hend, _hendLe, hlenValues⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hinner
  rw [attesterFirstInnerArrayLengthWord_toNat_of_decode
    (I := I) (elem := elem) hoffMax hreadFirst hinner hsizeSigned, hlenValues]
  exact Nat.le_of_not_gt hlenMax

theorem decodeABIArrayDynamicElems_first {ty : ABIType} {bytes : List UInt8}
    {base n : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIArrayDynamicElems? ty (n + 1) bytes base =
      some (values, endOffset)) :
    ∃ relativeOffset value valueEnd valuesRest restEnd,
      readNat? bytes base = some relativeOffset ∧
      decodeABIValue? ty bytes (base + relativeOffset) = some (value, valueEnd) ∧
      decodeABIArrayDynamicElemsFrom? ty n bytes base 32 ((n + 1) * 32)
          (max (base + (n + 1) * 32) valueEnd) =
        some (valuesRest, restEnd) ∧
      values = value :: valuesRest ∧
      endOffset = restEnd := by
  unfold decodeABIArrayDynamicElems? at h
  rw [decodeABIArrayDynamicElemsFrom?] at h
  cases hread : readNat? bytes base with
  | none =>
      simp [hread] at h
  | some relativeOffset =>
      simp [hread] at h
      cases hval : decodeABIValue? ty bytes (base + relativeOffset) with
      | none =>
          simp [hval] at h
      | some p =>
          rcases p with ⟨value, valueEnd⟩
          simp [hval] at h
          cases hrest :
              decodeABIArrayDynamicElemsFrom? ty n bytes base (0 + 32) ((n + 1) * 32)
                (max (base + (n + 1) * 32) valueEnd) with
          | none =>
              simp [hrest] at h
          | some q =>
              rcases q with ⟨valuesRest, restEnd⟩
              simp [hrest] at h
              rcases h with ⟨hvalues, hend⟩
              exact ⟨relativeOffset, value, valueEnd, valuesRest, restEnd,
                by simpa using hread, hval, by simpa using hrest,
                hvalues.symm, hend.symm⟩

theorem lookupNth?_some_length {α : Type} :
    ∀ {xs : List α} {i : Nat} {value : α},
      lookupNth? xs i = some value → i < xs.length
  | [], _, _, h => by simp [lookupNth?] at h
  | _ :: _, 0, _, _ => by simp
  | _ :: xs, i + 1, value, h => by
      have htail : lookupNth? xs i = some value := by
        simpa [lookupNth?] using h
      have hlt := lookupNth?_some_length htail
      simpa using Nat.succ_lt_succ hlt

theorem decodeABIArrayDynamicElemsFrom_lookup {ty : ABIType} {n : Nat}
    {bytes : List UInt8} {base headCursor headSize maxEnd : Nat}
    {values : List Value} {endOffset i : Nat} {value : Value}
    (h : decodeABIArrayDynamicElemsFrom? ty n bytes base headCursor headSize maxEnd =
      some (values, endOffset))
    (hlookup : lookupNth? values i = some value) :
    ∃ relativeOffset valueEnd,
      readNat? bytes (base + headCursor + 32 * i) = some relativeOffset ∧
      decodeABIValue? ty bytes (base + relativeOffset) = some (value, valueEnd) := by
  induction n generalizing headCursor maxEnd values endOffset i with
  | zero =>
      simp [decodeABIArrayDynamicElemsFrom?] at h
      rcases h with ⟨hvalues, _hend⟩
      cases hvalues
      simp [lookupNth?] at hlookup
  | succ n ih =>
      rw [decodeABIArrayDynamicElemsFrom?] at h
      cases hread : readNat? bytes (base + headCursor) with
      | none =>
          simp [hread] at h
      | some relativeOffset =>
          simp [hread] at h
          cases hval : decodeABIValue? ty bytes (base + relativeOffset) with
          | none =>
              simp [hval] at h
          | some p =>
              rcases p with ⟨headValue, valueEnd⟩
              simp [hval] at h
              cases hrest :
                  decodeABIArrayDynamicElemsFrom? ty n bytes base (headCursor + 32)
                    headSize (max maxEnd valueEnd) with
              | none =>
                  simp [hrest] at h
              | some q =>
                  rcases q with ⟨valuesRest, restEnd⟩
                  simp [hrest] at h
                  rcases h with ⟨hvalues, _hend⟩
                  cases hvalues
                  cases i with
                  | zero =>
                      simp [lookupNth?] at hlookup
                      cases hlookup
                      refine ⟨relativeOffset, valueEnd, ?_, hval⟩
                      simpa using hread
                  | succ i =>
                      have htail : lookupNth? valuesRest i = some value := by
                        simpa [lookupNth?] using hlookup
                      obtain ⟨tailOffset, tailEnd, htailRead, htailVal⟩ :=
                        ih hrest htail
                      refine ⟨tailOffset, tailEnd, ?_, htailVal⟩
                      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                        using htailRead

theorem decodeABIArrayDynamicElems_lookup {ty : ABIType} {n : Nat}
    {bytes : List UInt8} {base : Nat}
    {values : List Value} {endOffset i : Nat} {value : Value}
    (h : decodeABIArrayDynamicElems? ty n bytes base = some (values, endOffset))
    (hlookup : lookupNth? values i = some value) :
    ∃ relativeOffset valueEnd,
      readNat? bytes (base + 32 * i) = some relativeOffset ∧
      decodeABIValue? ty bytes (base + relativeOffset) = some (value, valueEnd) := by
  unfold decodeABIArrayDynamicElems? at h
  simpa [Nat.add_assoc] using
    decodeABIArrayDynamicElemsFrom_lookup (ty := ty) (n := n) (bytes := bytes)
      (base := base) (headCursor := 0) (headSize := n * 32)
      (maxEnd := base + n * 32) h hlookup

theorem decodeABIValue_nestedDynamicArray_lookup {elem : ABIType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset i : Nat}
    {inner : List Value}
    (hdec : decodeABIValue? (.dynamicArray (.dynamicArray elem)) bytes start =
      some (.array values, endOffset))
    (hlookup : lookupNth? values i = some (.array inner)) :
    ∃ len relativeOffset innerEnd,
      readNat? bytes start = some len ∧
      ¬ solcMaxLen DecodeMode.modern < len ∧
      i < len ∧
      readNat? bytes (start + 32 + 32 * i) = some relativeOffset ∧
      decodeABIValue? (.dynamicArray elem) bytes (start + 32 + relativeOffset) =
        some (.array inner, innerEnd) := by
  unfold decodeABIValue? at hdec
  cases hreadLen : readNat? bytes start with
  | none =>
      simp [hreadLen] at hdec
  | some len =>
      by_cases hlenMax : solcMaxU64 < len
      · simp [hreadLen, hlenMax, solcMaxLen] at hdec
      · simp [hreadLen, hlenMax, solcMaxLen, isDynamicABIType] at hdec
        cases hvals :
            decodeABIArrayDynamicElems? (.dynamicArray elem) len bytes (start + 32) with
        | none =>
            simp [hvals] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hvals] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            have hlookup0 : lookupNth? values i = some (.array inner) := hlookup
            obtain ⟨relativeOffset, innerEnd, hread, hinner⟩ :=
              decodeABIArrayDynamicElems_lookup
                (ty := .dynamicArray elem) (n := len) (bytes := bytes)
                (base := start + 32) hvals hlookup0
            have hi : i < len := by
              have hlt := lookupNth?_some_length hlookup0
              have hlen := decodeABIArrayDynamicElems_length hvals
              omega
            refine ⟨len, relativeOffset, innerEnd, (by simpa [hreadLen]), ?_, hi, ?_,
              hinner⟩
            · simpa [solcMaxLen] using hlenMax
            · simpa [Nat.add_assoc] using hread

theorem decodeABIValue_nestedDynamicArray_lookup_shape {elem : ABIType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset i : Nat}
    {value : Value}
    (hdec : decodeABIValue? (.dynamicArray (.dynamicArray elem)) bytes start =
      some (.array values, endOffset))
    (hlookup : lookupNth? values i = some value) :
    ∃ len relativeOffset inner innerEnd,
      value = .array inner ∧
      readNat? bytes start = some len ∧
      ¬ solcMaxLen DecodeMode.modern < len ∧
      i < len ∧
      readNat? bytes (start + 32 + 32 * i) = some relativeOffset ∧
      decodeABIValue? (.dynamicArray elem) bytes (start + 32 + relativeOffset) =
        some (.array inner, innerEnd) := by
  unfold decodeABIValue? at hdec
  cases hreadLen : readNat? bytes start with
  | none =>
      simp [hreadLen] at hdec
  | some len =>
      by_cases hlenMax : solcMaxU64 < len
      · simp [hreadLen, hlenMax, solcMaxLen] at hdec
      · simp [hreadLen, hlenMax, solcMaxLen, isDynamicABIType] at hdec
        cases hvals :
            decodeABIArrayDynamicElems? (.dynamicArray elem) len bytes (start + 32) with
        | none =>
            simp [hvals] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hvals] at hdec
            rcases hdec with ⟨hvalues, _hend⟩
            cases hvalues
            have hlookup0 : lookupNth? values i = some value := hlookup
            obtain ⟨relativeOffset, innerEnd, hread, hinnerValue⟩ :=
              decodeABIArrayDynamicElems_lookup
                (ty := .dynamicArray elem) (n := len) (bytes := bytes)
                (base := start + 32) hvals hlookup0
            obtain ⟨inner, hvalueArray⟩ :=
              decodeABIValue_dynamicArray_is_array hinnerValue
            have hi : i < len := by
              have hlt := lookupNth?_some_length hlookup0
              have hlen := decodeABIArrayDynamicElems_length hvals
              omega
            refine ⟨len, relativeOffset, inner, innerEnd, hvalueArray, (by simpa [hreadLen]),
              ?_, hi, ?_, ?_⟩
            · simpa [solcMaxLen] using hlenMax
            · simpa [Nat.add_assoc] using hread
            · simpa [hvalueArray] using hinnerValue

theorem decodeABIValue_nestedDynamicArray_first {elem : ABIType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (hdec : decodeABIValue? (.dynamicArray (.dynamicArray elem)) bytes start =
      some (.array values, endOffset))
    (hne : values.length ≠ 0) :
    ∃ n relativeOffset inner innerEnd valuesRest restEnd,
      readNat? bytes start = some (n + 1) ∧
      ¬ solcMaxLen DecodeMode.modern < n + 1 ∧
      readNat? bytes (start + 32) = some relativeOffset ∧
      decodeABIValue? (.dynamicArray elem) bytes (start + 32 + relativeOffset) =
        some (.array inner, innerEnd) ∧
      decodeABIArrayDynamicElemsFrom? (.dynamicArray elem) n bytes (start + 32) 32
          ((n + 1) * 32) (max (start + 32 + (n + 1) * 32) innerEnd) =
        some (valuesRest, restEnd) ∧
      values = .array inner :: valuesRest ∧
      endOffset = restEnd := by
  unfold decodeABIValue? at hdec
  cases hreadLen : readNat? bytes start with
  | none =>
      simp [hreadLen] at hdec
  | some len =>
      by_cases hlenMax : solcMaxU64 < len
      · simp [hreadLen, hlenMax, solcMaxLen] at hdec
      · simp [hreadLen, hlenMax, solcMaxLen, isDynamicABIType] at hdec
        cases hvals :
            decodeABIArrayDynamicElems? (.dynamicArray elem) len bytes (start + 32) with
        | none =>
            simp [hvals] at hdec
        | some p =>
            rcases p with ⟨values0, end0⟩
            simp [hvals] at hdec
            rcases hdec with ⟨hvalues, hend⟩
            cases hvalues
            cases hend
            have hvaluesLen := decodeABIArrayDynamicElems_length hvals
            cases len with
            | zero =>
                simp at hvaluesLen
                exfalso
                exact hne (by rw [hvaluesLen]; simp)
            | succ n =>
                obtain ⟨relativeOffset, value, valueEnd, valuesRest, restEnd,
                  hreadFirst, hvalue, hrest, hvalsShape, hrestEnd⟩ :=
                    decodeABIArrayDynamicElems_first (ty := .dynamicArray elem)
                      (bytes := bytes) (base := start + 32) (n := n)
                      hvals
                obtain ⟨inner, hinner⟩ := decodeABIValue_dynamicArray_is_array hvalue
                subst hinner
                exact ⟨n, relativeOffset, inner, valueEnd, valuesRest, restEnd,
                  rfl, by simpa [solcMaxLen] using hlenMax,
                  hreadFirst, hvalue, hrest,
                  hvalsShape, hrestEnd⟩

theorem attesterDecodeCalldata_twoDynamicArrays_first_decode {cd : ByteArray}
    {callargs : Store} {name0 name1 : Ident} {elem1 : ABIType}
    (hnames : name1 ≠ name0)
    (hdec : decodeCalldata [name0, name1] [.dynamicArray bytes32,
        .dynamicArray (.dynamicArray elem1)] cd = some callargs) :
    ∃ xs endOffset,
      decodeABIValue? (.dynamicArray bytes32) (cd.toList.drop 4)
          (calldataWord cd 4).toNat =
        some (.array xs, endOffset) ∧
      callargs.get? name0 = some (.array xs) := by
  unfold decodeCalldata at hdec
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType,
    bind, Option.bind] at hdec
  rcases hdec with ⟨_hlen4, _hhuge, _hargHuge, _htotalHuge, hdec⟩
  by_cases hshort : cd.toList.length - 4 < 64
  · simp [hshort] at hdec
  · simp [hshort] at hdec
    have hsz68 : 68 ≤ cd.size := by
      rw [htlen] at hshort
      omega
    cases hvals :
        decodeABIValues? [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
          (List.drop 4 cd.toList) 0 0 64 64 with
    | none =>
        simp [hvals] at hdec
    | some p =>
        rcases p with ⟨values, endOffset⟩
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
            · simp [hread0] at hvals
              cases hv0 : decodeABIValue? (.dynamicArray bytes32)
                  (List.drop 4 cd.toList) off0 with
              | none => simp [hv0] at hvals
              | some p0 =>
                  rcases p0 with ⟨v0, end0⟩
                  obtain ⟨xs, hv0arr⟩ := decodeABIValue_dynamicArray_is_array hv0
                  have hv0xs :
                      decodeABIValue? (.dynamicArray bytes32) (cd.toList.drop 4) off0 =
                        some (.array xs, end0) := by
                    simpa [hv0arr] using hv0
                  simp [hv0] at hvals
                  cases hrest :
                      decodeABIValues? [.dynamicArray (.dynamicArray elem1)]
                        (List.drop 4 cd.toList) 0 32 64 (max 64 end0) with
                  | none => simp [hrest] at hvals
                  | some prest =>
                      rcases prest with ⟨valuesRest, endRest⟩
                      simp [hrest] at hvals
                      rw [decodeABIValues?] at hrest
                      simp [isDynamicABIType, bind, Option.bind] at hrest
                      cases hread1 : readNat? (List.drop 4 cd.toList) 32 with
                      | none => simp [hread1] at hrest
                      | some off1 =>
                          by_cases hmax1 : solcMaxLen DecodeMode.modern < off1
                          · simp [hread1] at hrest
                            have hle : off1 ≤ solcMaxU64 := hrest.1
                            simp [solcMaxLen] at hmax1
                            omega
                          · simp [hread1] at hrest
                            cases hv1 :
                                decodeABIValue? (.dynamicArray (.dynamicArray elem1))
                                  (List.drop 4 cd.toList) off1 with
                            | none => simp [hv1] at hrest
                            | some p1 =>
                                rcases p1 with ⟨v1, end1⟩
                                obtain ⟨ys, hv1arr⟩ :=
                                  decodeABIValue_dynamicArray_is_array hv1
                                simp [hv1] at hrest
                                rcases hrest with ⟨_hoff1le, hrestEq⟩
                                simp [decodeABIValues?] at hrestEq
                                rcases hrestEq with ⟨hvaluesRestEq, _hendRestEq⟩
                                rcases hvals with ⟨_hoff0le, hvalsEq⟩
                                rcases hvalsEq with ⟨hvaluesEq, _hendEq⟩
                                cases hvaluesRestEq
                                rw [← hvaluesEq, hv0arr, hv1arr] at hdec
                                simp [decodeCalldata.insertValues] at hdec
                                cases hdec
                                have hreadOff0 := readNat_drop4_zero_eq_calldataWord
                                  (cd := cd) (by omega : 36 ≤ cd.size)
                                rw [hread0] at hreadOff0
                                cases hreadOff0
                                refine ⟨xs, end0, ?_, ?_⟩
                                · exact hv0xs
                                · rw [Std.HashMap.get?_eq_getElem?]
                                  rw [Std.HashMap.getElem?_insert]
                                  simp [hnames]

theorem attesterDecodeCalldata_twoDynamicArrays_second_decode {cd : ByteArray}
    {callargs : Store} {name0 name1 : Ident} {elem1 : ABIType}
    (hdec : decodeCalldata [name0, name1] [.dynamicArray bytes32,
        .dynamicArray (.dynamicArray elem1)] cd = some callargs) :
    ∃ ys endOffset,
      decodeABIValue? (.dynamicArray (.dynamicArray elem1)) (cd.toList.drop 4)
          (calldataWord cd 36).toNat =
        some (.array ys, endOffset) ∧
      callargs.get? name1 = some (.array ys) := by
  unfold decodeCalldata at hdec
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType,
    bind, Option.bind] at hdec
  rcases hdec with ⟨_hlen4, _hhuge, _hargHuge, _htotalHuge, hdec⟩
  by_cases hshort : cd.toList.length - 4 < 64
  · simp [hshort] at hdec
  · simp [hshort] at hdec
    have hsz68 : 68 ≤ cd.size := by
      rw [htlen] at hshort
      omega
    cases hvals :
        decodeABIValues? [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
          (List.drop 4 cd.toList) 0 0 64 64 with
    | none =>
        simp [hvals] at hdec
    | some p =>
        rcases p with ⟨values, endOffset⟩
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
            · simp [hread0] at hvals
              cases hv0 : decodeABIValue? (.dynamicArray bytes32)
                  (List.drop 4 cd.toList) off0 with
              | none => simp [hv0] at hvals
              | some p0 =>
                  rcases p0 with ⟨v0, end0⟩
                  obtain ⟨xs, hv0arr⟩ := decodeABIValue_dynamicArray_is_array hv0
                  simp [hv0] at hvals
                  cases hrest :
                      decodeABIValues? [.dynamicArray (.dynamicArray elem1)]
                        (List.drop 4 cd.toList) 0 32 64 (max 64 end0) with
                  | none => simp [hrest] at hvals
                  | some prest =>
                      rcases prest with ⟨valuesRest, endRest⟩
                      simp [hrest] at hvals
                      rw [decodeABIValues?] at hrest
                      simp [isDynamicABIType, bind, Option.bind] at hrest
                      cases hread1 : readNat? (List.drop 4 cd.toList) 32 with
                      | none => simp [hread1] at hrest
                      | some off1 =>
                          by_cases hmax1 : solcMaxLen DecodeMode.modern < off1
                          · simp [hread1] at hrest
                            have hle : off1 ≤ solcMaxU64 := hrest.1
                            simp [solcMaxLen] at hmax1
                            omega
                          · simp [hread1] at hrest
                            cases hv1 :
                                decodeABIValue? (.dynamicArray (.dynamicArray elem1))
                                  (List.drop 4 cd.toList) off1 with
                            | none => simp [hv1] at hrest
                            | some p1 =>
                                rcases p1 with ⟨v1, end1⟩
                                obtain ⟨ys, hv1arr⟩ :=
                                  decodeABIValue_dynamicArray_is_array hv1
                                have hv1ys :
                                    decodeABIValue? (.dynamicArray (.dynamicArray elem1))
                                        (cd.toList.drop 4) off1 =
                                      some (.array ys, end1) := by
                                  simpa [hv1arr] using hv1
                                simp [hv1] at hrest
                                rcases hrest with ⟨_hoff1le, hrestEq⟩
                                simp [decodeABIValues?] at hrestEq
                                rcases hrestEq with ⟨hvaluesRestEq, _hendRestEq⟩
                                rcases hvals with ⟨_hoff0le, hvalsEq⟩
                                rcases hvalsEq with ⟨hvaluesEq, _hendEq⟩
                                cases hvaluesRestEq
                                rw [← hvaluesEq, hv0arr, hv1arr] at hdec
                                simp [decodeCalldata.insertValues] at hdec
                                cases hdec
                                have hreadOff1 := readNat_drop4_32_eq_calldataWord
                                  (cd := cd) hsz68
                                rw [hread1] at hreadOff1
                                cases hreadOff1
                                refine ⟨ys, end1, ?_, ?_⟩
                                · exact hv1ys
                                · simp [Std.HashMap.get?_eq_getElem?]

theorem attesterDecode_multiRevoke_first_inner_decode (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids : List Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hne : schemaUids.length ≠ 0) :
    ∃ n relativeOffset inner innerEnd valuesRest restEnd,
      readNat? (I.calldata.toList.drop 4) (calldataWord I.calldata 36).toNat =
        some (n + 1) ∧
      ¬ solcMaxLen DecodeMode.modern < n + 1 ∧
      readNat? (I.calldata.toList.drop 4) ((calldataWord I.calldata 36).toNat + 32) =
        some relativeOffset ∧
      decodeABIValue? (.dynamicArray bytes32) (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
        some (.array inner, innerEnd) ∧
      decodeABIArrayDynamicElemsFrom? (.dynamicArray bytes32) n
          (I.calldata.toList.drop 4) ((calldataWord I.calldata 36).toNat + 32) 32
          ((n + 1) * 32)
          (max ((calldataWord I.calldata 36).toNat + 32 + (n + 1) * 32) innerEnd) =
        some (valuesRest, restEnd) ∧
      schemaUids = .array inner :: valuesRest ∧
      restEnd = restEnd := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  obtain ⟨ys, endOffset, hsecond, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_second_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaUids") (elem1 := bytes32) hdec'
  have hys : ys = schemaUids := by
    cases Option.some.inj (hget.symm.trans hSchemaUids)
    rfl
  have hneYs : ys.length ≠ 0 := by
    intro hzero
    exact hne (by rw [← hys, hzero])
  obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
      hlen, hlenMax, hreadFirst, hinner, hrest, hshape, _hend⟩ :=
    decodeABIValue_nestedDynamicArray_first (elem := bytes32) hsecond hneYs
  refine ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
    hlen, hlenMax, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [Nat.add_assoc] using hreadFirst
  · simpa [Nat.add_assoc] using hinner
  · simpa [Nat.add_assoc] using hrest
  · rw [← hys, hshape]

theorem attesterDecode_multiRevoke_inner_decode_at (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids inner : List Value} {idx : Nat}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookup : lookupNth? schemaUids idx = some (.array inner)) :
    ∃ len relativeOffset innerEnd,
      readNat? (I.calldata.toList.drop 4) (calldataWord I.calldata 36).toNat =
        some len ∧
      ¬ solcMaxLen DecodeMode.modern < len ∧
      idx < len ∧
      readNat? (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + 32 * idx) =
        some relativeOffset ∧
      decodeABIValue? (.dynamicArray bytes32) (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
        some (.array inner, innerEnd) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  obtain ⟨ys, endOffset, hsecond, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_second_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaUids") (elem1 := bytes32) hdec'
  have hys : ys = schemaUids := by
    cases Option.some.inj (hget.symm.trans hSchemaUids)
    rfl
  have hlookupYs : lookupNth? ys idx = some (.array inner) := by
    rw [hys]
    exact hlookup
  obtain ⟨len, relativeOffset, innerEnd, hlen, hlenMax, hidx, hread,
      hinner⟩ :=
    decodeABIValue_nestedDynamicArray_lookup (elem := bytes32) hsecond hlookupYs
  refine ⟨len, relativeOffset, innerEnd, hlen, hlenMax, hidx, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hread
  · simpa [Nat.add_assoc] using hinner

theorem attesterDecode_multiRevoke_schema_norm (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemas : List Value}
    {idx : Nat} {schema : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemas : callargs.get? "schemas" = some (.array schemas))
    (hlookup : lookupNth? schemas idx = some schema) :
    normalizeRawBoolWord? schema = .ok schema := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  obtain ⟨xs, endOffset, hfirst, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_first_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaUids") (elem1 := bytes32)
      (by decide) hdec'
  have hxs : xs = schemas := by
    cases Option.some.inj (hget.symm.trans hSchemas)
    rfl
  have hlookupXs : lookupNth? xs idx = some schema := by
    rw [hxs]
    exact hlookup
  obtain ⟨word, hshape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4) (start := (calldataWord I.calldata 4).toNat)
      (endOffset := endOffset) hfirst (lookupNth?_some_length hlookupXs)
  rw [hlookupXs] at hshape
  cases hshape
  simp [normalizeRawBoolWord?]

theorem attesterDecode_multiRevoke_schemaUids_shape (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaUids : List Value}
    {idx : Nat} {value : Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiRevokeTransition v).params.map Param.name)
        (transitionSignature (multiRevokeTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaUids : callargs.get? "schemaUids" = some (.array schemaUids))
    (hlookup : lookupNth? schemaUids idx = some value) :
    ∃ uids,
      value = .array uids ∧
      uids.length < 2 ^ 256 ∧
      (∀ {j uid}, lookupNth? uids j = some uid →
        normalizeRawBoolWord? uid = .ok uid) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaUids"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray bytes32)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiRevokeTransition, transitionSignature,
      bytes32Array, bytes32NestedArray] using hdec
  obtain ⟨ys, endOffset, hsecond, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_second_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaUids") (elem1 := bytes32) hdec'
  have hys : ys = schemaUids := by
    cases Option.some.inj (hget.symm.trans hSchemaUids)
    rfl
  have hlookupYs : lookupNth? ys idx = some value := by
    rw [hys]
    exact hlookup
  obtain ⟨_len, _relativeOffset, inner, innerEnd, hvalue, _hlenRead, _hlenMax, _hidx,
      _hread, hinner⟩ :=
    decodeABIValue_nestedDynamicArray_lookup_shape (elem := bytes32) hsecond hlookupYs
  have hinner' :
      decodeABIValue? (.dynamicArray abiBytes32) (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + _relativeOffset) =
        some (.array inner, innerEnd) := by
    simpa [bytes32, bytes32Width, abiBytes32, abiBytes32Width] using hinner
  obtain ⟨innerLen, _hreadInnerLen, hinnerLenMax, _hend, _hendLe, hinnerLen⟩ :=
    decodeABIValue_dynamicArray_elem32_facts hinner'
  have hinnerBound : inner.length < 2 ^ 256 := by
    have hle : inner.length ≤ solcMaxU64 := by
      rw [hinnerLen]
      exact Nat.le_of_not_gt hinnerLenMax
    norm_num [solcMaxU64] at hle ⊢
    omega
  refine ⟨inner, hvalue, hinnerBound, ?_⟩
  intro j uid hlookupUid
  obtain ⟨word, huidShape⟩ :=
    decodeABIValue_dynamicArray_bytes32_lookup_shape
      (bytes := I.calldata.toList.drop 4)
      (start := (calldataWord I.calldata 36).toNat + 32 + _relativeOffset)
      (endOffset := innerEnd) hinner'
      (lookupNth?_some_length hlookupUid)
  rw [hlookupUid] at huidShape
  cases huidShape
  simp [normalizeRawBoolWord?]

theorem attesterDecode_multiAttest_first_inner_decode (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaInputs : List Value}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaInputs : callargs.get? "schemaInputs" = some (.array schemaInputs))
    (hne : schemaInputs.length ≠ 0) :
    ∃ n relativeOffset inner innerEnd valuesRest restEnd,
      readNat? (I.calldata.toList.drop 4) (calldataWord I.calldata 36).toNat =
        some (n + 1) ∧
      ¬ solcMaxLen DecodeMode.modern < n + 1 ∧
      readNat? (I.calldata.toList.drop 4) ((calldataWord I.calldata 36).toNat + 32) =
        some relativeOffset ∧
      decodeABIValue? (.dynamicArray uint256) (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
        some (.array inner, innerEnd) ∧
      decodeABIArrayDynamicElemsFrom? (.dynamicArray uint256) n
          (I.calldata.toList.drop 4) ((calldataWord I.calldata 36).toNat + 32) 32
          ((n + 1) * 32)
          (max ((calldataWord I.calldata 36).toNat + 32 + (n + 1) * 32) innerEnd) =
        some (valuesRest, restEnd) ∧
      schemaInputs = .array inner :: valuesRest ∧
      restEnd = restEnd := by
  have hdec' :
      decodeCalldata ["schemas", "schemaInputs"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray uint256)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiAttestTransition, transitionSignature,
      bytes32Array, uint256Array, uint256NestedArray] using hdec
  obtain ⟨ys, endOffset, hsecond, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_second_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaInputs") (elem1 := uint256) hdec'
  have hys : ys = schemaInputs := by
    cases Option.some.inj (hget.symm.trans hSchemaInputs)
    rfl
  have hneYs : ys.length ≠ 0 := by
    intro hzero
    exact hne (by rw [← hys, hzero])
  obtain ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
      hlen, hlenMax, hreadFirst, hinner, hrest, hshape, _hend⟩ :=
    decodeABIValue_nestedDynamicArray_first (elem := uint256) hsecond hneYs
  refine ⟨n, relativeOffset, inner, innerEnd, valuesRest, restEnd,
    hlen, hlenMax, ?_, ?_, ?_, ?_, rfl⟩
  · simpa [Nat.add_assoc] using hreadFirst
  · simpa [Nat.add_assoc] using hinner
  · simpa [Nat.add_assoc] using hrest
  · rw [← hys, hshape]

theorem attesterDecode_multiAttest_inner_decode_at (v : AttesterImmutables)
    {I : ExecutionEnv} {callargs : Store} {schemaInputs inner : List Value} {idx : Nat}
    (hdec : decodeCalldataWithMode (config v).abiDecodeMode
        ((multiAttestTransition v).params.map Param.name)
        (transitionSignature (multiAttestTransition v)).paramTypes I.calldata =
      some callargs)
    (hSchemaInputs : callargs.get? "schemaInputs" = some (.array schemaInputs))
    (hlookup : lookupNth? schemaInputs idx = some (.array inner)) :
    ∃ len relativeOffset innerEnd,
      readNat? (I.calldata.toList.drop 4) (calldataWord I.calldata 36).toNat =
        some len ∧
      ¬ solcMaxLen DecodeMode.modern < len ∧
      idx < len ∧
      readNat? (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + 32 * idx) =
        some relativeOffset ∧
      decodeABIValue? (.dynamicArray uint256) (I.calldata.toList.drop 4)
          ((calldataWord I.calldata 36).toNat + 32 + relativeOffset) =
        some (.array inner, innerEnd) := by
  have hdec' :
      decodeCalldata ["schemas", "schemaInputs"]
        [.dynamicArray bytes32, .dynamicArray (.dynamicArray uint256)] I.calldata =
      some callargs := by
    simpa [decodeCalldataWithMode, config, multiAttestTransition, transitionSignature,
      bytes32Array, uint256Array, uint256NestedArray] using hdec
  obtain ⟨ys, endOffset, hsecond, hget⟩ :=
    attesterDecodeCalldata_twoDynamicArrays_second_decode
      (cd := I.calldata) (callargs := callargs)
      (name0 := "schemas") (name1 := "schemaInputs") (elem1 := uint256) hdec'
  have hys : ys = schemaInputs := by
    cases Option.some.inj (hget.symm.trans hSchemaInputs)
    rfl
  have hlookupYs : lookupNth? ys idx = some (.array inner) := by
    rw [hys]
    exact hlookup
  obtain ⟨len, relativeOffset, innerEnd, hlen, hlenMax, hidx, hread,
      hinner⟩ :=
    decodeABIValue_nestedDynamicArray_lookup (elem := uint256) hsecond hlookupYs
  refine ⟨len, relativeOffset, innerEnd, hlen, hlenMax, hidx, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hread
  · simpa [Nat.add_assoc] using hinner

end Benchmarks.EAS.Attester
