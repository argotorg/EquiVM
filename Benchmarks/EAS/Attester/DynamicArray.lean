import Benchmarks.EAS.Attester.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Reasoning.Reach

theorem swap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
          1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap9_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.EAS.Attester

/-! Shared facts for the solc dynamic-array ABI decoder used by the multi entrypoints. -/

/-- Trusted jump-destination fact for the successful length-word check in the shared dynamic-array decoder. -/
axiom attesterDynamicArrayLengthOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2054⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful array-length max check. -/
axiom attesterDynamicArrayLengthMaxOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2076⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful first-array payload bound check. -/
axiom attesterDynamicArrayPayloadOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2102⟩ : UInt256) = true

/-- Trusted jump-destination fact for returning from the first dynamic-array decoder call. -/
axiom attesterDynamic2FirstArrayReturnJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2161⟩ : UInt256) = true

/-- Trusted jump-destination fact for the second top-level dynamic-offset max check. -/
axiom attesterDynamic2SecondOffsetOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2191⟩ : UInt256) = true

/-- Trusted jump-destination fact for returning from the second dynamic-array decoder call. -/
axiom attesterDynamic2SecondArrayReturnJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨2203⟩ : UInt256) = true

/-- Trusted jump-destination fact for the short-circuited `multiRevoke` body length guard. -/
axiom attesterMultiRevokeLengthGuardJoinJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨206⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful `multiRevoke` body length guard. -/
axiom attesterMultiRevokeLengthGuardOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨236⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful `multiRevoke` outer-array allocation bound. -/
axiom attesterMultiRevokeAllocLengthMaxOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨261⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiRevoke` outer-array initializer loop head. -/
axiom attesterMultiRevokeOuterArrayInitLoopJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨291⟩ : UInt256) = true

/-- Trusted jump-destination fact for the short-circuited `multiAttest` body length guard. -/
axiom attesterMultiAttestLengthGuardJoinJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨844⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful `multiAttest` body length guard. -/
axiom attesterMultiAttestLengthGuardOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨874⟩ : UInt256) = true

/-- Trusted jump-destination fact for the successful `multiAttest` outer-array allocation bound. -/
axiom attesterMultiAttestAllocLengthMaxOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨899⟩ : UInt256) = true

/-- Trusted jump-destination fact for the `multiAttest` outer-array initializer loop head. -/
axiom attesterMultiAttestOuterArrayInitLoopJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨929⟩ : UInt256) = true

def attesterRequireSelectorMem : ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft (⟨3036299187⟩ : UInt256) ⟨224⟩)).write
    0 solcFreePtrMem 128 32

theorem attesterRequireSelectorMem_size : attesterRequireSelectorMem.size = 160 := by
  unfold attesterRequireSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size,
    solcFreePtrMem_size]

theorem attesterRequireSelectorMem_read64 :
    attesterRequireSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold attesterRequireSelectorMem
  rw [toByteArray_write_read_below_of_gap _ _ 128 64
    (by rw [solcFreePtrMem_size])
    (by omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  exact solcFreePtrMem_read64

theorem attesterRequireSelectorMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ attesterRequireSelectorMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (attesterRequireSelectorMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [attesterRequireSelectorMem_size]; decide) (by decide)
    attesterRequireSelectorMem_read64

theorem decodeABIArrayDynamicElemsFrom_length {ty : ABIType} {n : Nat}
    {bytes : List UInt8} {base headCursor headSize maxEnd : Nat}
    {values : List Value} {endOffset : Nat}
    (h : decodeABIArrayDynamicElemsFrom? ty n bytes base headCursor headSize maxEnd =
      some (values, endOffset)) :
    values.length = n := by
  induction n generalizing headCursor maxEnd values endOffset with
  | zero =>
      simp [decodeABIArrayDynamicElemsFrom?] at h
      rcases h with ⟨hvalues, _⟩
      cases hvalues
      rfl
  | succ n ih =>
      rw [decodeABIArrayDynamicElemsFrom?] at h
      cases hread : readNat? bytes (base + headCursor) with
      | none => simp [hread] at h
      | some relativeOffset =>
          simp [hread] at h
          cases hval : decodeABIValue? ty bytes (base + relativeOffset) with
          | none => simp [hval] at h
          | some p =>
              rcases p with ⟨value, valueEnd⟩
              simp [hval] at h
              cases hrest :
                  decodeABIArrayDynamicElemsFrom? ty n bytes base (headCursor + 32)
                    headSize (max maxEnd valueEnd) with
              | none => simp [hrest] at h
              | some q =>
                  rcases q with ⟨valuesRest, restEnd⟩
                  simp [hrest] at h
                  rcases h with ⟨hvalues, _hend⟩
                  cases hvalues
                  rw [List.length_cons, ih hrest]

theorem decodeABIArrayDynamicElems_length {ty : ABIType} {n : Nat}
    {bytes : List UInt8} {base : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIArrayDynamicElems? ty n bytes base = some (values, endOffset)) :
    values.length = n := by
  unfold decodeABIArrayDynamicElems? at h
  exact decodeABIArrayDynamicElemsFrom_length h

theorem decodeABIValue_dynamicArray_dynamic_facts {elem : ABIType}
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray (.dynamicArray elem)) bytes start =
      some (.array values, endOffset)) :
    ∃ len, readNat? bytes start = some len ∧ ¬ solcMaxU64 < len ∧ values.length = len := by
  unfold decodeABIValue? at h
  cases hread : readNat? bytes start with
  | none => simp [hread] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at h
      · simp [hread, hmax, isDynamicABIType] at h
        cases hvals : decodeABIArrayDynamicElems? (.dynamicArray elem) len bytes (start + 32) with
        | none => simp [hvals] at h
        | some p =>
            rcases p with ⟨vals, end'⟩
            simp [hvals] at h
            rcases h with ⟨hvalues, _hend⟩
            refine ⟨len, rfl, hmax, ?_⟩
            rw [← hvalues]
            exact decodeABIArrayDynamicElems_length hvals

theorem decodeABIValue_dynamicArray_bytes32_facts
    {bytes : List UInt8} {start : Nat} {values : List Value} {endOffset : Nat}
    (h : decodeABIValue? (.dynamicArray bytes32) bytes start =
      some (.array values, endOffset)) :
    ∃ len, readNat? bytes start = some len ∧ ¬ solcMaxU64 < len ∧ values.length = len := by
  unfold decodeABIValue? at h
  cases hread : readNat? bytes start with
  | none => simp [hread] at h
  | some len =>
      by_cases hmax : solcMaxU64 < len
      · simp [hread, hmax] at h
      · simp [hread, hmax, bytes32, isDynamicABIType] at h
        cases hstatic :
            decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width)) len 32 bytes
              (start + 32) with
        | none =>
            change ((decodeABIArrayStaticElems?
                (ABIType.elem (ElemType.bytes bytes32Width)) len 32 bytes (start + 32)).bind
                  fun p => some (Value.array p.1, p.2)) =
                    some (Value.array values, endOffset) at h
            rw [hstatic] at h
            simp at h
        | some p =>
            rcases p with ⟨vals, end'⟩
            change ((decodeABIArrayStaticElems?
                (ABIType.elem (ElemType.bytes bytes32Width)) len 32 bytes (start + 32)).bind
                  fun p => some (Value.array p.1, p.2)) =
                    some (Value.array values, endOffset) at h
            rw [hstatic] at h
            simp at h
            rcases h with ⟨hvalues, _hend⟩
            refine ⟨len, rfl, hmax, ?_⟩
            rw [← hvalues]
            obtain ⟨_hend, _hle, hlen⟩ :=
              decodeABIArrayStaticElems_elem32_facts
                (elem := .bytes bytes32Width) (readNat?_some_length hread) hstatic
            exact hlen

theorem attesterDecodeCalldata_twoDynamicArrays_none_totalHuge {cd : ByteArray}
    {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hbig : 2 ^ 255 ≤ cd.size) :
    decodeCalldata [name0, name1] [.dynamicArray elem0, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  by_cases hlt4 : cd.toList.length < 4
  · rw [if_pos hlt4]
  · rw [if_neg hlt4]
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hdyn :
        [ABIType.dynamicArray elem0, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
              isDynamicABIType = true ∧
            2 ^ 255 ≤ cd.toList.length := by
      exact ⟨by simp [isDynamicABIType], by rw [htlen]; exact hbig⟩
    rw [if_pos hdyn]

theorem attesterDecodeCalldata_twoDynamicArrays_none_firstLengthShort {cd : ByteArray}
    {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hshort : cd.size < 4 + (calldataWord cd 4).toNat + 32) :
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
      have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen :
          readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat = none := by
        unfold readNat? readWord? readBytes?
        have hlen :
            ¬ (((cd.toList.drop 4).drop (calldataWord cd 4).toNat).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, List.length_drop, htlen]
          omega
        rw [if_neg hlen]
        rfl
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, hreadOff, hoffMax, hreadLen]

theorem attesterDecodeCalldata_twoDynamicArrays_none_firstLengthHuge {cd : ByteArray}
    {name0 name1 : Ident} {elem0 elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenHuge : solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
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
      have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoffMax hlenWord
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, hreadOff, hoffMax, hreadLen,
        hlenHuge]

theorem attesterDecodeCalldata_twoDynamicArrays_none_firstBytes32PayloadShort {cd : ByteArray}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoffMax : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload : cd.size <
      4 + (calldataWord cd 4).toNat + 32 +
        32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) :
    decodeCalldata [name0, name1] [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
      have hreadOff := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoffMax hlenWord
      have hstaticNone :
          decodeABIArrayStaticElems? bytes32
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
            (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) = none := by
        cases hstatic :
            decodeABIArrayStaticElems? bytes32
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
              (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) with
        | none => rfl
        | some p =>
            rcases p with ⟨values, endOffset⟩
            have hstart :
                (calldataWord cd 4).toNat + 32 ≤ (cd.toList.drop 4).length := by
              rw [List.length_drop, htlen]
              omega
            obtain ⟨hend, hle, _hlen⟩ :=
              decodeABIArrayStaticElems_elem32_facts
                (elem := .bytes bytes32Width) hstart hstatic
            rw [hend] at hle
            rw [List.length_drop, htlen] at hle
            omega
      have hstaticSize : staticABIEncodedSize? bytes32 = some 32 := by
        native_decide
      have hstaticSize' :
          staticABIEncodedSize? (ABIType.elem (ElemType.bytes bytes32Width)) = some 32 := by
        simpa [bytes32] using hstaticSize
      have hstaticNone' :
          decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width))
            (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
            (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) = none := by
        simpa [bytes32] using hstaticNone
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, bytes32, hreadOff, hoffMax, hreadLen,
        hlenMax, hstaticSize', hstaticNone']

theorem readNat_drop4_32_eq_calldataWord {cd : ByteArray}
    (hsz68 : 68 ≤ cd.size) :
    readNat? (cd.toList.drop 4) 32 = some (calldataWord cd 36).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) 32 32 =
      some (((cd.toList.drop 4).drop 32).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hlen : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_pos hlen]
  rw [hread]
  have hword :
      bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    have h := decode_word_at_eq cd 36 (by omega) (by norm_num)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

theorem readNat_drop4_at_eq_calldataWord {cd : ByteArray} {off : Nat}
    (hlenWord : 4 + off + 32 ≤ cd.size) :
    readNat? (cd.toList.drop 4) off = some (calldataWord cd (4 + off)).toNat := by
  unfold readNat? readWord?
  have hread : readBytes? (cd.toList.drop 4) off 32 =
      some (((cd.toList.drop 4).drop off).take 32) := by
    unfold readBytes?
    have htlen : cd.toList.length = cd.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    have hlen : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [if_pos hlen]
  rw [hread]
  have hword :
      bytesToWord (((cd.toList.drop 4).drop off).take 32) =
        calldataWord cd (4 + off) := by
    have h := decode_word_at_eq_any cd (4 + off) hlenWord
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  simp only [Option.bind, bind, hword]
  rfl

theorem readNat_drop4_at_none_of_short {cd : ByteArray} {off : Nat}
    (hshort : cd.size < 4 + off + 32) :
    readNat? (cd.toList.drop 4) off = none := by
  unfold readNat? readWord? readBytes?
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen :
      ¬ (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  rw [if_neg hlen]
  rfl

theorem attesterDecodeCalldata_twoDynamicArrays_lengths {cd : ByteArray} {callargs : Store}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hne : (name1 == name0) = false)
    (hdec : decodeCalldata [name0, name1] [.dynamicArray bytes32,
        .dynamicArray (.dynamicArray elem1)] cd = some callargs) :
    ∃ xs ys : List Value,
      callargs.get? name0 = some (.array xs) ∧
      callargs.get? name1 = some (.array ys) ∧
      xs.length = (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ∧
      ys.length = (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat := by
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
              cases hv0 : decodeABIValue? (.dynamicArray bytes32) (List.drop 4 cd.toList) off0 with
              | none => simp [hv0] at hvals
              | some p0 =>
                  rcases p0 with ⟨v0, end0⟩
                  obtain ⟨xs, hv0arr⟩ := decodeABIValue_dynamicArray_is_array hv0
                  have hv0xs :
                      decodeABIValue? (.dynamicArray bytes32) (List.drop 4 cd.toList) off0 =
                        some (.array xs, end0) := by
                    simpa [hv0arr] using hv0
                  obtain ⟨len0, hreadLen0, _hlen0Max, hxsLen⟩ :=
                    decodeABIValue_dynamicArray_bytes32_facts hv0xs
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
                                obtain ⟨ys, hv1arr⟩ := decodeABIValue_dynamicArray_is_array hv1
                                have hv1ys :
                                    decodeABIValue? (.dynamicArray (.dynamicArray elem1))
                                      (List.drop 4 cd.toList) off1 =
                                      some (.array ys, end1) := by
                                  simpa [hv1arr] using hv1
                                obtain ⟨len1, hreadLen1, _hlen1Max, hysLen⟩ :=
                                  decodeABIValue_dynamicArray_dynamic_facts hv1ys
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
                                have hreadOff1 := readNat_drop4_32_eq_calldataWord
                                  (cd := cd) hsz68
                                rw [hread1] at hreadOff1
                                cases hreadOff1
                                have hlen0Word :
                                    readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat =
                                      some (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat := by
                                  have hbound := readNat?_some_length hreadLen0
                                  exact readNat_drop4_at_eq_calldataWord
                                    (cd := cd) (off := (calldataWord cd 4).toNat) (by
                                      rw [List.length_drop, htlen] at hbound
                                      omega)
                                have hlen0Eq :
                                    len0 =
                                      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
                                  Option.some.inj (hreadLen0.symm.trans hlen0Word)
                                have hlen1Word :
                                    readNat? (cd.toList.drop 4) (calldataWord cd 36).toNat =
                                      some (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat := by
                                  have hbound := readNat?_some_length hreadLen1
                                  exact readNat_drop4_at_eq_calldataWord
                                    (cd := cd) (off := (calldataWord cd 36).toNat) (by
                                      rw [List.length_drop, htlen] at hbound
                                      omega)
                                have hlen1Eq :
                                    len1 =
                                      (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat :=
                                  Option.some.inj (hreadLen1.symm.trans hlen1Word)
                                refine ⟨xs, ys, ?_, ?_, ?_, ?_⟩
                                · simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem_insert, hne]
                                · simp [Std.HashMap.get?_eq_getElem?]
                                · exact hxsLen.trans hlen0Eq
                                · exact hysLen.trans hlen1Eq

theorem decodeABIArrayDynamicElemsFrom_none_head_short {ty : ABIType}
    {bytes : List UInt8} {base headCursor headSize maxEnd n : Nat}
    (hshort : bytes.length < base + headCursor + 32 * (n + 1)) :
    decodeABIArrayDynamicElemsFrom? ty (n + 1) bytes base headCursor headSize maxEnd = none := by
  induction n generalizing headCursor maxEnd with
  | zero =>
      unfold decodeABIArrayDynamicElemsFrom?
      have hread : readNat? bytes (base + headCursor) = none := by
        unfold readNat? readWord? readBytes?
        have hlen : ¬ ((bytes.drop (base + headCursor)).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [if_neg hlen]
        rfl
      simp [hread]
  | succ n ih =>
      unfold decodeABIArrayDynamicElemsFrom?
      cases hread : readNat? bytes (base + headCursor) with
      | none => simp
      | some relativeOffset =>
          simp
          cases hval : decodeABIValue? ty bytes (base + relativeOffset) with
          | none => simp
          | some p =>
              rcases p with ⟨value, valueEnd⟩
              simp
              have hshort' : bytes.length < base + (headCursor + 32) + 32 * (n + 1) := by
                omega
              rw [ih (headCursor := headCursor + 32)
                  (maxEnd := max maxEnd valueEnd) hshort']
              simp

theorem decodeABIArrayDynamicElems_none_head_short {ty : ABIType}
    {bytes : List UInt8} {base n : Nat}
    (hshort : bytes.length < base + 32 * (n + 1)) :
    decodeABIArrayDynamicElems? ty (n + 1) bytes base = none := by
  simpa [decodeABIArrayDynamicElems?, Nat.mul_comm] using
    decodeABIArrayDynamicElemsFrom_none_head_short
      (ty := ty) (bytes := bytes) (base := base) (headCursor := 0)
      (headSize := (n + 1) * 32) (maxEnd := base + (n + 1) * 32)
      (by simpa [Nat.add_assoc] using hshort)

theorem attesterDecodeCalldata_twoDynamicArrays_none_secondOffsetHuge {cd : ByteArray}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlenWord : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord cd 4).toNat + 32 +
          32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤
        cd.size)
    (hoff1Huge : solcMaxU64 < (calldataWord cd 36).toNat) :
    decodeCalldata [name0, name1] [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
      have hread0 := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen0 := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoff0Max hlenWord
      have hread1 := readNat_drop4_32_eq_calldataWord (cd := cd) hsz68
      have hstaticSize : staticABIEncodedSize? bytes32 = some 32 := by
        native_decide
      have hstaticSize' :
          staticABIEncodedSize? (ABIType.elem (ElemType.bytes bytes32Width)) = some 32 := by
        simpa [bytes32] using hstaticSize
      obtain ⟨values0, hstatic0, _hlen0⟩ :=
        decodeABIArrayStaticElems_bytes32_exists_of_length
          (n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
          (bytes := cd.toList.drop 4)
          (start := (calldataWord cd 4).toNat + 32) (by
            rw [List.length_drop, htlen]
            omega)
      have hstatic0' :
          decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width))
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
              (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) =
            some (values0,
              (calldataWord cd 4).toNat + 32 +
                32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) := by
        simpa [bytes32] using hstatic0
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, bytes32, hread0, hoff0Max,
        hreadLen0, hlen0Max, hstaticSize', hstatic0', hread1, hoff1Huge]

theorem attesterDecodeCalldata_twoDynamicArrays_none_secondLengthShort {cd : ByteArray}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlen0Word : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord cd 4).toNat + 32 +
          32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤
        cd.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord cd 36).toNat)
    (hshort1 : cd.size < 4 + (calldataWord cd 36).toNat + 32) :
    decodeCalldata [name0, name1] [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
      have hread0 := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen0 := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoff0Max hlen0Word
      have hread1 := readNat_drop4_32_eq_calldataWord (cd := cd) hsz68
      have hreadLen1 :
          readNat? (cd.toList.drop 4) (calldataWord cd 36).toNat = none :=
        readNat_drop4_at_none_of_short
          (cd := cd) (off := (calldataWord cd 36).toNat) hshort1
      have hstaticSize : staticABIEncodedSize? bytes32 = some 32 := by
        native_decide
      have hstaticSize' :
          staticABIEncodedSize? (ABIType.elem (ElemType.bytes bytes32Width)) = some 32 := by
        simpa [bytes32] using hstaticSize
      obtain ⟨values0, hstatic0, _hlen0⟩ :=
        decodeABIArrayStaticElems_bytes32_exists_of_length
          (n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
          (bytes := cd.toList.drop 4)
          (start := (calldataWord cd 4).toNat + 32) (by
            rw [List.length_drop, htlen]
            omega)
      have hstatic0' :
          decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width))
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
              (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) =
            some (values0,
              (calldataWord cd 4).toNat + 32 +
                32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) := by
        simpa [bytes32] using hstatic0
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, bytes32, hread0, hoff0Max,
        hreadLen0, hlen0Max, hstaticSize', hstatic0', hread1, hoff1Max, hreadLen1]

theorem attesterDecodeCalldata_twoDynamicArrays_none_secondLengthHuge {cd : ByteArray}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlen0Word : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord cd 4).toNat + 32 +
          32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤
        cd.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord cd 36).toNat)
    (hlen1Word : 4 + (calldataWord cd 36).toNat + 32 ≤ cd.size)
    (hlen1Huge : solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat) :
    decodeCalldata [name0, name1] [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
      have hread0 := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen0 := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoff0Max hlen0Word
      have hread1 := readNat_drop4_32_eq_calldataWord (cd := cd) hsz68
      have hreadLen1 := readNat_drop4_at_eq_calldataWord
        (cd := cd) (off := (calldataWord cd 36).toNat) hlen1Word
      have hstaticSize : staticABIEncodedSize? bytes32 = some 32 := by
        native_decide
      have hstaticSize' :
          staticABIEncodedSize? (ABIType.elem (ElemType.bytes bytes32Width)) = some 32 := by
        simpa [bytes32] using hstaticSize
      obtain ⟨values0, hstatic0, _hlen0⟩ :=
        decodeABIArrayStaticElems_bytes32_exists_of_length
          (n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
          (bytes := cd.toList.drop 4)
          (start := (calldataWord cd 4).toNat + 32) (by
            rw [List.length_drop, htlen]
            omega)
      have hstatic0' :
          decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width))
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
              (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) =
            some (values0,
              (calldataWord cd 4).toNat + 32 +
                32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) := by
        simpa [bytes32] using hstatic0
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, bytes32, hread0, hoff0Max,
        hreadLen0, hlen0Max, hstaticSize', hstatic0', hread1, hoff1Max, hreadLen1,
        hlen1Huge]

theorem attesterDecodeCalldata_twoDynamicArrays_none_secondPayloadShort {cd : ByteArray}
    {name0 name1 : Ident} {elem1 : ABIType}
    (hsz68 : 68 ≤ cd.size)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord cd 4).toNat)
    (hlen0Word : 4 + (calldataWord cd 4).toNat + 32 ≤ cd.size)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
    (hpayload0 :
      4 + (calldataWord cd 4).toNat + 32 +
          32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤
        cd.size)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord cd 36).toNat)
    (hlen1Word : 4 + (calldataWord cd 36).toNat + 32 ≤ cd.size)
    (hlen1Max : ¬ solcMaxU64 <
      (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat)
    (hpayload1 :
      cd.size <
        4 + (calldataWord cd 36).toNat + 32 +
          32 * (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat) :
    decodeCalldata [name0, name1] [.dynamicArray bytes32, .dynamicArray (.dynamicArray elem1)]
        cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  by_cases hdyn :
      ([ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].any
          isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length)
  · rw [if_pos hdyn]
  · rw [if_neg hdyn]
    by_cases hargsHuge :
        [ABIType.dynamicArray bytes32, ABIType.dynamicArray (ABIType.dynamicArray elem1)].isEmpty =
            false ∧
          2 ^ 255 ≤ (cd.toList.drop 4).length
    · rw [if_pos hargsHuge]
    · rw [if_neg hargsHuge]
      rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
      have hread0 := readNat_drop4_zero_eq_calldataWord (cd := cd) (by omega : 36 ≤ cd.size)
      have hreadLen0 := readNat_drop4_dynamic_eq_calldataWord
        (cd := cd) hoff0Max hlen0Word
      have hread1 := readNat_drop4_32_eq_calldataWord (cd := cd) hsz68
      have hreadLen1 := readNat_drop4_at_eq_calldataWord
        (cd := cd) (off := (calldataWord cd 36).toNat) hlen1Word
      have hlen1Pos :
          0 < (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat := by
        by_contra hzero
        have hzero' :
            (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat = 0 := by
          omega
        rw [hzero'] at hpayload1
        omega
      obtain ⟨n, hlen1Eq⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen1Pos)
      have hdynamicNone :
          decodeABIArrayDynamicElems? (.dynamicArray elem1)
              (calldataWord cd (4 + (calldataWord cd 36).toNat)).toNat
              (cd.toList.drop 4) ((calldataWord cd 36).toNat + 32) = none := by
        rw [hlen1Eq]
        apply decodeABIArrayDynamicElems_none_head_short
        rw [List.length_drop, htlen]
        omega
      have hstaticSize : staticABIEncodedSize? bytes32 = some 32 := by
        native_decide
      have hstaticSize' :
          staticABIEncodedSize? (ABIType.elem (ElemType.bytes bytes32Width)) = some 32 := by
        simpa [bytes32] using hstaticSize
      obtain ⟨values0, hstatic0, _hlen0⟩ :=
        decodeABIArrayStaticElems_bytes32_exists_of_length
          (n := (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat)
          (bytes := cd.toList.drop 4)
          (start := (calldataWord cd 4).toNat + 32) (by
            rw [List.length_drop, htlen]
            omega)
      have hstatic0' :
          decodeABIArrayStaticElems? (ABIType.elem (ElemType.bytes bytes32Width))
              (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat 32
              (cd.toList.drop 4) ((calldataWord cd 4).toNat + 32) =
            some (values0,
              (calldataWord cd 4).toNat + 32 +
                32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat) := by
        simpa [bytes32] using hstatic0
      simp [decodeCalldata.decodeArgs, decodeABIValues?, decodeABIValue?, isDynamicABIType,
        abiTupleHeadSize?, bind, Option.bind, solcMaxLen, bytes32, hread0, hoff0Max,
        hreadLen0, hlen0Max, hstaticSize', hstatic0', hread1, hoff1Max, hreadLen1,
        hlen1Max, hdynamicNone]

theorem attesterDynamicArrayStart_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat =
      4 + (calldataWord I.calldata 4).toNat := by
  change (((⟨4⟩ : UInt256) + calldataWord I.calldata 4).toNat =
    4 + (calldataWord I.calldata 4).toNat)
  rw [uadd_toNat]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
    omega)

abbrev attesterFirstArrayStartWord (I : ExecutionEnv) : UInt256 :=
  UInt256.add ⟨4⟩ (calldataWord I.calldata 4)

abbrev attesterFirstArrayLengthWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (attesterFirstArrayStartWord I).toNat

abbrev attesterFirstArrayPayloadEndWord (I : ExecutionEnv) : UInt256 :=
  (attesterFirstArrayStartWord I +
      UInt256.shiftLeft (attesterFirstArrayLengthWord I) ⟨5⟩) + ⟨32⟩

abbrev attesterSecondArrayStartWord (I : ExecutionEnv) : UInt256 :=
  UInt256.add ⟨4⟩ (calldataWord I.calldata 36)

abbrev attesterSecondArrayLengthWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata (attesterSecondArrayStartWord I).toNat

abbrev attesterSecondArrayPayloadEndWord (I : ExecutionEnv) : UInt256 :=
  (attesterSecondArrayStartWord I +
      UInt256.shiftLeft (attesterSecondArrayLengthWord I) ⟨5⟩) + ⟨32⟩

abbrev attesterMultiOuterArrayAllocEndWord (I : ExecutionEnv) : UInt256 :=
  (⟨128⟩ : UInt256) +
    ((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) (attesterFirstArrayLengthWord I))

abbrev attesterMultiOuterArrayLenMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (attesterFirstArrayLengthWord I)).write 0 solcFreePtrMem 128 32

abbrev attesterMultiOuterArrayAllocMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (attesterMultiOuterArrayAllocEndWord I)).write 0
    (attesterMultiOuterArrayLenMem I) 64 32

abbrev attesterMloadWord (mem : ByteArray) (aw off : UInt256) : UInt256 :=
  if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))

abbrev attesterMloadAw (aw off : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)

abbrev attesterMultiOuterArrayInitFreeWord (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadWord mem aw ⟨64⟩

abbrev attesterMultiOuterArrayInitAwAfterMload (aw : UInt256) : UInt256 :=
  attesterMloadAw aw ⟨64⟩

abbrev attesterMultiOuterArrayInitFreeMem (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray
      ((⟨64⟩ : UInt256) + attesterMultiOuterArrayInitFreeWord mem aw)).write 0 mem 64 32

abbrev attesterMultiOuterArrayInitFreeAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (attesterMultiOuterArrayInitAwAfterMload aw).toNat 64 32)

abbrev attesterMultiOuterArrayInitZeroMem (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0
    (attesterMultiOuterArrayInitFreeMem mem aw)
    (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32

abbrev attesterMultiOuterArrayInitZeroAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiOuterArrayInitFreeAw aw).toNat
      (attesterMultiOuterArrayInitFreeWord mem aw).toNat 32)

abbrev attesterMultiOuterArrayInitOffsetWord (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMultiOuterArrayInitFreeWord mem aw + (⟨32⟩ : UInt256)

abbrev attesterMultiOuterArrayInitOffsetMem (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨96⟩ : UInt256)).write 0
    (attesterMultiOuterArrayInitZeroMem mem aw)
    (attesterMultiOuterArrayInitOffsetWord mem aw).toNat 32

abbrev attesterMultiOuterArrayInitOffsetAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiOuterArrayInitZeroAw mem aw).toNat
      (attesterMultiOuterArrayInitOffsetWord mem aw).toNat 32)

abbrev attesterMultiOuterArrayInitStepMem
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterMultiOuterArrayInitFreeWord mem aw)).write 0
    (attesterMultiOuterArrayInitOffsetMem mem aw) slot.toNat 32

abbrev attesterMultiOuterArrayInitStepAw
    (slot : UInt256) (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiOuterArrayInitOffsetAw mem aw).toNat slot.toNat 32)

theorem attesterDynamicArrayStart31_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨31⟩).toNat =
      4 + (calldataWord I.calldata 4).toNat + 31 := by
  rw [uadd_toNat]
  rw [attesterDynamicArrayStart_toNat (I := I) hoffMax]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
    omega)

theorem attesterSecondArrayStart_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat =
      4 + (calldataWord I.calldata 36).toNat := by
  change (((⟨4⟩ : UInt256) + calldataWord I.calldata 36).toNat =
    4 + (calldataWord I.calldata 36).toNat)
  rw [uadd_toNat]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
    omega)

theorem attesterFirstArrayLengthWord_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    (attesterFirstArrayLengthWord I).toNat =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
  unfold attesterFirstArrayLengthWord
  rw [attesterDynamicArrayStart_toNat (I := I) hoffMax]

theorem attesterSecondArrayLengthWord_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    (attesterSecondArrayLengthWord I).toNat =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  unfold attesterSecondArrayLengthWord
  rw [attesterSecondArrayStart_toNat (I := I) hoffMax]

theorem attesterFirstArrayLengthWord_isZero_of_nat_eq_zero {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hzero :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat = 0) :
    UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨1⟩ := by
  have hword : attesterFirstArrayLengthWord I = ⟨0⟩ := by
    apply u256_inj
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoffMax, hzero]
    decide
  rw [hword]
  decide

theorem attesterFirstArrayLengthWord_isZero_of_nat_ne_zero {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnonzero :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0) :
    UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩ := by
  apply isZero_eq_zero_of_ne
  intro hword
  have hnat := congrArg UInt256.toNat hword
  rw [attesterFirstArrayLengthWord_toNat (I := I) hoffMax] at hnat
  exact hnonzero (by simpa using hnat)

theorem attesterArrayLengthWords_eq_one_of_nat_eq {I : ExecutionEnv}
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (heq :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨1⟩ := by
  have hword : attesterSecondArrayLengthWord I = attesterFirstArrayLengthWord I := by
    apply u256_inj
    rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1Max,
      attesterFirstArrayLengthWord_toNat (I := I) hoff0Max, heq]
  rw [hword]
  exact uInt256_eq_self _

theorem attesterArrayLengthWords_eq_zero_of_nat_ne {I : ExecutionEnv}
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hne :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro hone
  have hword := uInt256_eq_one_eq hone
  have hnat := congrArg UInt256.toNat hword
  rw [attesterSecondArrayLengthWord_toNat (I := I) hoff1Max,
    attesterFirstArrayLengthWord_toNat (I := I) hoff0Max] at hnat
  exact hne hnat

theorem attesterSecondArrayStart31_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    ((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨31⟩).toNat =
      4 + (calldataWord I.calldata 36).toNat + 31 := by
  rw [uadd_toNat]
  rw [attesterSecondArrayStart_toNat (I := I) hoffMax]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe ⊢
    omega)

theorem attesterShiftLeft5_toNat_of_le (a : UInt256)
    (ha : a.toNat ≤ solcMaxU64) :
    (UInt256.shiftLeft a ⟨5⟩).toNat = 32 * a.toNat := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨5⟩ : UInt256).val ≥ 256))]
  change (((a.toNat <<< (⟨5⟩ : UInt256).val.val) % UInt256.size)) = 32 * a.toNat
  rw [show (⟨5⟩ : UInt256).val.val = 5 by decide]
  rw [Nat.shiftLeft_eq]
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt (by
    norm_num [solcMaxU64, UInt256.size] at ha ⊢
    omega)

theorem attesterFirstArrayPayloadEnd_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    (attesterFirstArrayPayloadEndWord I).toNat =
      4 + (calldataWord I.calldata 4).toNat +
        32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat + 32 := by
  have hstartToNat : (attesterFirstArrayStartWord I).toNat =
      4 + (calldataWord I.calldata 4).toNat :=
    attesterDynamicArrayStart_toNat (I := I) hoffMax
  have hlenLeRaw : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64 := by
    unfold attesterFirstArrayLengthWord
    rw [hstartToNat]
    exact Nat.le_of_not_gt hlenMax
  have hlenRawEq :
      (attesterFirstArrayLengthWord I).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    unfold attesterFirstArrayLengthWord
    rw [hstartToNat]
  have hshiftToNat :
      (UInt256.shiftLeft (attesterFirstArrayLengthWord I) ⟨5⟩).toNat =
        32 * (attesterFirstArrayLengthWord I).toNat :=
    attesterShiftLeft5_toNat_of_le (attesterFirstArrayLengthWord I) hlenLeRaw
  unfold attesterFirstArrayPayloadEndWord
  rw [uadd_toNat]
  have hstartShift :
      (attesterFirstArrayStartWord I +
          UInt256.shiftLeft (attesterFirstArrayLengthWord I) ⟨5⟩).toNat =
        4 + (calldataWord I.calldata 4).toNat +
          32 * (attesterFirstArrayLengthWord I).toNat := by
    rw [uadd_toNat, hstartToNat, hshiftToNat]
    exact Nat.mod_eq_of_lt (by
      have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
        Nat.le_of_not_gt hoffMax
      have hlenLe : (attesterFirstArrayLengthWord I).toNat ≤ solcMaxU64 := hlenLeRaw
      norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLe ⊢
      omega)
  rw [hstartShift]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [hlenRawEq]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    have hlenLe : (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≤
        solcMaxU64 := Nat.le_of_not_gt hlenMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLe ⊢
    omega)

theorem attesterSecondArrayPayloadEnd_toNat {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    (attesterSecondArrayPayloadEndWord I).toNat =
      4 + (calldataWord I.calldata 36).toNat +
        32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat + 32 := by
  have hstartToNat : (attesterSecondArrayStartWord I).toNat =
      4 + (calldataWord I.calldata 36).toNat :=
    attesterSecondArrayStart_toNat (I := I) hoffMax
  have hlenLeRaw : (attesterSecondArrayLengthWord I).toNat ≤ solcMaxU64 := by
    unfold attesterSecondArrayLengthWord
    rw [hstartToNat]
    exact Nat.le_of_not_gt hlenMax
  have hlenRawEq :
      (attesterSecondArrayLengthWord I).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
    unfold attesterSecondArrayLengthWord
    rw [hstartToNat]
  have hshiftToNat :
      (UInt256.shiftLeft (attesterSecondArrayLengthWord I) ⟨5⟩).toNat =
        32 * (attesterSecondArrayLengthWord I).toNat :=
    attesterShiftLeft5_toNat_of_le (attesterSecondArrayLengthWord I) hlenLeRaw
  unfold attesterSecondArrayPayloadEndWord
  rw [uadd_toNat]
  have hstartShift :
      (attesterSecondArrayStartWord I +
          UInt256.shiftLeft (attesterSecondArrayLengthWord I) ⟨5⟩).toNat =
        4 + (calldataWord I.calldata 36).toNat +
          32 * (attesterSecondArrayLengthWord I).toNat := by
    rw [uadd_toNat, hstartToNat, hshiftToNat]
    exact Nat.mod_eq_of_lt (by
      have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
        Nat.le_of_not_gt hoffMax
      have hlenLe : (attesterSecondArrayLengthWord I).toNat ≤ solcMaxU64 := hlenLeRaw
      norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLe ⊢
      omega)
  rw [hstartShift]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [hlenRawEq]
  exact Nat.mod_eq_of_lt (by
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    have hlenLe : (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≤
        solcMaxU64 := Nat.le_of_not_gt hlenMax
    norm_num [solcMaxU64, UInt256.size] at hoffLe hlenLe ⊢
    omega)

theorem attesterDynamicArrayPayloadGuardGtOne_of_short {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hsize : I.calldata.size < UInt256.size)
    (hpayloadShort : I.calldata.size <
      4 + (calldataWord I.calldata 4).toNat + 32 +
        32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    UInt256.gt (attesterFirstArrayPayloadEndWord I) (UInt256.ofNat I.calldata.size) =
      ⟨1⟩ := by
  apply ugt_one
  rw [attesterFirstArrayPayloadEnd_toNat (I := I) hoffMax hlenMax]
  rw [ulit_toNat' I.calldata.size hsize]
  omega

theorem attesterDynamicArrayPayloadGuardGtZero_of_ok {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hsize : I.calldata.size < UInt256.size)
    (hpayloadOk :
      4 + (calldataWord I.calldata 4).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
        ≤ I.calldata.size) :
    UInt256.gt (attesterFirstArrayPayloadEndWord I) (UInt256.ofNat I.calldata.size) =
      ⟨0⟩ := by
  apply ugt_zero
  rw [attesterFirstArrayPayloadEnd_toNat (I := I) hoffMax hlenMax]
  rw [ulit_toNat' I.calldata.size hsize]
  omega

theorem attesterDynamicArrayLengthGuardSltZero_of_short {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  have hstart31 := attesterDynamicArrayStart31_toNat (I := I) hoffMax
  apply slt_lit_zero (m := I.calldata.size)
  · exact hsizeSigned
  · rw [hstart31]
    omega
  · rw [hstart31]
    have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64] at hoffLe ⊢
    omega

theorem attesterDynamicArrayLengthGuardSltZero_of_sizeHuge {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hbig : 2 ^ 255 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  apply slt_zero_low_high
  · rw [attesterDynamicArrayStart31_toNat (I := I) hoffMax]
    have hoffLe : (calldataWord I.calldata 4).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64] at hoffLe ⊢
    omega
  · rw [ulit_toNat' I.calldata.size hsize]
    exact hbig

theorem attesterSecondArrayLengthGuardSltZero_of_short {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
  have hstart31 := attesterSecondArrayStart31_toNat (I := I) hoffMax
  apply slt_lit_zero (m := I.calldata.size)
  · exact hsizeSigned
  · rw [hstart31]
    omega
  · rw [hstart31]
    have hoffLe : (calldataWord I.calldata 36).toNat ≤ solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    norm_num [solcMaxU64] at hoffLe ⊢
    omega

theorem attesterSecondArrayPayloadGuardGtOne_of_short {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hsize : I.calldata.size < UInt256.size)
    (hpayloadShort : I.calldata.size <
      4 + (calldataWord I.calldata 36).toNat + 32 +
        32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    UInt256.gt (attesterSecondArrayPayloadEndWord I) (UInt256.ofNat I.calldata.size) =
      ⟨1⟩ := by
  apply ugt_one
  rw [attesterSecondArrayPayloadEnd_toNat (I := I) hoffMax hlenMax]
  rw [ulit_toNat' I.calldata.size hsize]
  omega

theorem attesterSecondArrayPayloadGuardGtZero_of_ok {I : ExecutionEnv}
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hsize : I.calldata.size < UInt256.size)
    (hpayloadOk :
      4 + (calldataWord I.calldata 36).toNat + 32 +
          32 * (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
        ≤ I.calldata.size) :
    UInt256.gt (attesterSecondArrayPayloadEndWord I) (UInt256.ofNat I.calldata.size) =
      ⟨0⟩ := by
  apply ugt_zero
  rw [attesterSecondArrayPayloadEnd_toNat (I := I) hoffMax hlenMax]
  rw [ulit_toNat' I.calldata.size hsize]
  omega

theorem attesterX_dynamicArrayLengthGuardOk {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 4),
        UInt256.ofNat I.calldata.size, ret, calldataWord I.calldata 4,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2038⟩ := hreach
  have hstart31ToNat := attesterDynamicArrayStart31_toNat (I := I) hoffMax
  have hslt :
      UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply slt_lit_one_low (m := I.calldata.size)
    · exact hsizeSigned
    · rw [hstart31ToNat]
      omega
  exact ⟨_, _, evm_run rd2038 with [
    raw jumpdest (by attester_decode_at v, ⟨2038⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2039⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2040⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2041⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2042⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2044⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2045⟩, 0x01, .ADD) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2046⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2054⟩ (by attester_decode_at v, ⟨2047⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2050⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (attesterDynamicArrayLengthOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamicArrayLengthGuardReverts {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt :
      UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2038⟩ := hreach
  exact evm_run rd2038 with [
    raw jumpdest (by attester_decode_at v, ⟨2038⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2039⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2040⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2041⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2042⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2044⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2045⟩, 0x01, .ADD) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2046⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2054⟩ (by attester_decode_at v, ⟨2047⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2050⟩, 0x57, .JUMPI)
      (by rw [hslt]) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2051⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2052⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2053⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamicArrayLengthMaxOk {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 4),
        UInt256.ofNat I.calldata.size, ret, calldataWord I.calldata 4,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2054⟩ := hreach
  have hstartToNat := attesterDynamicArrayStart_toNat (I := I) hoffMax
  have hgt :
      UInt256.gt (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hstartToNat, hmaxToNat]
    exact Nat.le_of_not_gt hlenMax
  exact ⟨_, _, evm_run rd2054 with [
    raw jumpdest (by attester_decode_at v, ⟨2054⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2055⟩, 0x50, .POP) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2056⟩, 0x81, .DUP2) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2057⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2058⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2060⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2062⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2064⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2065⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2066⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2067⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2068⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2076⟩ (by attester_decode_at v, ⟨2069⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2072⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt
              (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterDynamicArrayLengthMaxOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamicArrayLengthMaxHugeReverts {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenHuge : solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 4),
        UInt256.ofNat I.calldata.size, ret, calldataWord I.calldata 4,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2054⟩ := hreach
  have hstartToNat := attesterDynamicArrayStart_toNat (I := I) hoffMax
  have hgt :
      UInt256.gt (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hstartToNat, hmaxToNat]
    exact hlenHuge
  exact evm_run rd2054 with [
    raw jumpdest (by attester_decode_at v, ⟨2054⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2055⟩, 0x50, .POP) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2056⟩, 0x81, .DUP2) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2057⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2058⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2060⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2062⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2064⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2065⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2066⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2067⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2068⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2076⟩ (by attester_decode_at v, ⟨2069⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2072⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt
              (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩
        rw [hgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2073⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2074⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2075⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamicArrayPayloadGuardOk {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hgt :
      UInt256.gt
        (((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) +
            UInt256.shiftLeft
              (calldataWord I.calldata
                (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat) ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2076⟩ := hreach
  exact ⟨_, _, evm_run rd2076 with [
    raw jumpdest (by attester_decode_at v, ⟨2076⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2077⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2079⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2080⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2081⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2082⟩, 0x50, .POP) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2083⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2084⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2086⟩, 0x82, .DUP3) (by evm_ov),
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2087⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2089⟩, 0x1b, .SHL) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2090⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2091⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2092⟩, 0x01, .ADD) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2093⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2094⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2095⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2098⟩, 0x57, .JUMPI)
      (by rw [hgt]; decide) (attesterDynamicArrayPayloadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamicArrayPayloadGuardReverts {ret decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hgt :
      UInt256.gt
        (((UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) +
            UInt256.shiftLeft
              (calldataWord I.calldata
                (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat) ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ret, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2076⟩ := hreach
  exact evm_run rd2076 with [
    raw jumpdest (by attester_decode_at v, ⟨2076⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2077⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2079⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2080⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2081⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2082⟩, 0x50, .POP) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2083⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2084⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2086⟩, 0x82, .DUP3) (by evm_ov),
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2087⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2089⟩, 0x1b, .SHL) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2090⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2091⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2092⟩, 0x01, .ADD) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2093⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2094⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2095⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2098⟩, 0x57, .JUMPI)
      (by rw [hgt]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2099⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2100⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2101⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamicArrayPayloadOkToFirstReturn {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 4), UInt256.ofNat I.calldata.size,
        ⟨2161⟩, calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2161⟩ : UInt256)
      [attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2102⟩ := hreach
  exact ⟨_, _, evm_run rd2102 with [
    raw jumpdest (by attester_decode_at v, ⟨2102⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2103⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2104⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2105⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2106⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2107⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2108⟩, 0x56, .JUMP)
      (attesterDynamic2FirstArrayReturnJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2SecondOffsetOk {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2161⟩ : UInt256)
      [attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2191⟩ : UInt256)
      [calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2161⟩ := hreach
  have hgt :
      UInt256.gt (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hmaxToNat]
    exact Nat.le_of_not_gt hoff1Max
  exact ⟨_, _, evm_run rd2161 with [
    raw jumpdest (by attester_decode_at v, ⟨2161⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2162⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap6 (by attester_decode_at v, ⟨2163⟩, 0x95, .SWAP6) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2164⟩, 0x50, .POP) (by evm_ov),
    raw swap4 (by attester_decode_at v, ⟨2165⟩, 0x93, .SWAP4) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2166⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2167⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2168⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2170⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2171⟩, 0x01, .ADD) (by simp),
    raw calldataload (by attester_decode_at v, ⟨2172⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2173⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2175⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2177⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2179⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2180⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2181⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2182⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2183⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2191⟩ (by attester_decode_at v, ⟨2184⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2187⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (calldataWord I.calldata 36)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterDynamic2SecondOffsetOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2SecondOffsetHugeReverts {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoff1Huge : solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2161⟩ : UInt256)
      [attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        calldataWord I.calldata 4, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2161⟩ := hreach
  have hgt :
      UInt256.gt (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hmaxToNat]
    exact hoff1Huge
  exact evm_run rd2161 with [
    raw jumpdest (by attester_decode_at v, ⟨2161⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2162⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap6 (by attester_decode_at v, ⟨2163⟩, 0x95, .SWAP6) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2164⟩, 0x50, .POP) (by evm_ov),
    raw swap4 (by attester_decode_at v, ⟨2165⟩, 0x93, .SWAP4) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2166⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2167⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2168⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2170⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2171⟩, 0x01, .ADD) (by simp),
    raw calldataload (by attester_decode_at v, ⟨2172⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2173⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2175⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2177⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2179⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2180⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2181⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2182⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2183⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2191⟩ (by attester_decode_at v, ⟨2184⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2187⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (calldataWord I.calldata 36)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩
        rw [hgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2188⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2189⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2190⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_dynamic2SecondArrayDecoderEntry {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2191⟩ : UInt256)
      [calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2191⟩ := hreach
  exact ⟨_, _, evm_run rd2191 with [
    raw jumpdest (by attester_decode_at v, ⟨2191⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨2203⟩ (by attester_decode_at v, ⟨2192⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2195⟩, 0x87, .DUP8) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2196⟩, 0x82, .DUP3) (by evm_ov),
    raw dup9 (by attester_decode_at v, ⟨2197⟩, 0x88, .DUP9) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2198⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨2038⟩ (by attester_decode_at v, ⟨2199⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2202⟩, 0x56, .JUMP)
      (attesterDynamicArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_secondArrayLengthGuardOk {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeSigned : I.calldata.size < 2 ^ 255)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 36),
        UInt256.ofNat I.calldata.size, ⟨2203⟩, calldataWord I.calldata 36,
        ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2038⟩ := hreach
  have hstart31ToNat := attesterSecondArrayStart31_toNat (I := I) hoffMax
  have hslt :
      UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply slt_lit_one_low (m := I.calldata.size)
    · exact hsizeSigned
    · rw [hstart31ToNat]
      omega
  exact ⟨_, _, evm_run rd2038 with [
    raw jumpdest (by attester_decode_at v, ⟨2038⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2039⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2040⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2041⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2042⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2044⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2045⟩, 0x01, .ADD) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2046⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2054⟩ (by attester_decode_at v, ⟨2047⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2050⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (attesterDynamicArrayLengthOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_secondArrayLengthGuardReverts {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt :
      UInt256.slt ((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2038⟩ : UInt256)
      [UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2038⟩ := hreach
  exact evm_run rd2038 with [
    raw jumpdest (by attester_decode_at v, ⟨2038⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2039⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2040⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2041⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2042⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2044⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2045⟩, 0x01, .ADD) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2046⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2054⟩ (by attester_decode_at v, ⟨2047⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2050⟩, 0x57, .JUMPI)
      (by rw [hslt]) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2051⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2052⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2053⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_secondArrayLengthMaxOk {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenMax : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 36),
        UInt256.ofNat I.calldata.size, ⟨2203⟩, calldataWord I.calldata 36,
        ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2054⟩ := hreach
  have hstartToNat := attesterSecondArrayStart_toNat (I := I) hoffMax
  have hgt :
      UInt256.gt (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hstartToNat, hmaxToNat]
    exact Nat.le_of_not_gt hlenMax
  exact ⟨_, _, evm_run rd2054 with [
    raw jumpdest (by attester_decode_at v, ⟨2054⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2055⟩, 0x50, .POP) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2056⟩, 0x81, .DUP2) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2057⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2058⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2060⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2062⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2064⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2065⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2066⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2067⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2068⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2076⟩ (by attester_decode_at v, ⟨2069⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2072⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt
              (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterDynamicArrayLengthMaxOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_secondArrayLengthMaxHugeReverts {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoffMax : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenHuge : solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2054⟩ : UInt256)
      [⟨0⟩, ⟨0⟩, UInt256.add ⟨4⟩ (calldataWord I.calldata 36),
        UInt256.ofNat I.calldata.size, ⟨2203⟩, calldataWord I.calldata 36,
        ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2054⟩ := hreach
  have hstartToNat := attesterSecondArrayStart_toNat (I := I) hoffMax
  have hgt :
      UInt256.gt (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [hstartToNat, hmaxToNat]
    exact hlenHuge
  exact evm_run rd2054 with [
    raw jumpdest (by attester_decode_at v, ⟨2054⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2055⟩, 0x50, .POP) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2056⟩, 0x81, .DUP2) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2057⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2058⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2060⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2062⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2064⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2065⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2066⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2067⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2068⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2076⟩ (by attester_decode_at v, ⟨2069⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2072⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt
              (calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩
        rw [hgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2073⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2074⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2075⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_secondArrayPayloadGuardOk {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hgt :
      UInt256.gt
        (((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) +
            UInt256.shiftLeft
              (calldataWord I.calldata
                (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat) ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2076⟩ := hreach
  exact ⟨_, _, evm_run rd2076 with [
    raw jumpdest (by attester_decode_at v, ⟨2076⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2077⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2079⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2080⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2081⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2082⟩, 0x50, .POP) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2083⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2084⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2086⟩, 0x82, .DUP3) (by evm_ov),
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2087⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2089⟩, 0x1b, .SHL) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2090⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2091⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2092⟩, 0x01, .ADD) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2093⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2094⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2095⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2098⟩, 0x57, .JUMPI)
      (by rw [hgt]; decide) (attesterDynamicArrayPayloadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_secondArrayPayloadGuardReverts {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hgt :
      UInt256.gt
        (((UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) +
            UInt256.shiftLeft
              (calldataWord I.calldata
                (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat) ⟨5⟩) + ⟨32⟩)
        (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2076⟩ : UInt256)
      [calldataWord I.calldata (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)).toNat, ⟨0⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2076⟩ := hreach
  exact evm_run rd2076 with [
    raw jumpdest (by attester_decode_at v, ⟨2076⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2077⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2079⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2080⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2081⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2082⟩, 0x50, .POP) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2083⟩, 0x83, .DUP4) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2084⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2086⟩, 0x82, .DUP3) (by evm_ov),
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2087⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2089⟩, 0x1b, .SHL) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2090⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2091⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2092⟩, 0x01, .ADD) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2093⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2094⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2095⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2098⟩, 0x57, .JUMPI)
      (by rw [hgt]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2099⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2100⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2101⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_secondArrayPayloadOkToSecondReturn {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        UInt256.add ⟨4⟩ (calldataWord I.calldata 36), UInt256.ofNat I.calldata.size,
        ⟨2203⟩, calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2203⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2102⟩ := hreach
  exact ⟨_, _, evm_run rd2102 with [
    raw jumpdest (by attester_decode_at v, ⟨2102⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2103⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2104⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2105⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2106⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2107⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2108⟩, 0x56, .JUMP)
      (attesterDynamic2SecondArrayReturnJumpdest v) (by evm_ov)]⟩

theorem attesterX_dynamic2DecodeDone {decodeOk retPc : UInt256}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hdecodeJumpdest : (D_J (patchedRuntime v) 0).contains decodeOk = true)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2203⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        calldataWord I.calldata 36, ⟨0⟩, ⟨0⟩, attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, decodeOk, retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) decodeOk
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        retPc, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2203⟩ := hreach
  exact ⟨_, _, evm_run rd2203 with [
    raw jumpdest (by attester_decode_at v, ⟨2203⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap6 (by attester_decode_at v, ⟨2204⟩, 0x95, .SWAP6) (by evm_ov),
    raw swap9 (by attester_decode_at v, ⟨2205⟩, 0x98, .SWAP9) (by evm_ov),
    raw swap5 (by attester_decode_at v, ⟨2206⟩, 0x94, .SWAP5) (by evm_ov),
    raw swap8 (by attester_decode_at v, ⟨2207⟩, 0x97, .SWAP8) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2208⟩, 0x50, .POP) (by evm_ov),
    raw swap6 (by attester_decode_at v, ⟨2209⟩, 0x95, .SWAP6) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2210⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2211⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2212⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2213⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2214⟩, 0x56, .JUMP)
      hdecodeJumpdest (by evm_ov)]⟩

theorem attesterX_multiRevokeDecodedToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨92⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd92⟩ := hreach
  exact ⟨_, _, evm_run rd92 with [
    raw jumpdest (by attester_decode_at v, ⟨92⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨192⟩ (by attester_decode_at v, ⟨93⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨96⟩, 0x56, .JUMP)
      (attesterMultiRevokeBodyJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeLengthZeroReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd192⟩ := hreach
  exact evm_run rd192 with [
    raw jumpdest (by attester_decode_at v, ⟨192⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨193⟩, 0x82, .DUP3) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨194⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨195⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨196⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨206⟩ (by attester_decode_at v, ⟨197⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨200⟩, 0x57, .JUMPI)
      (by rw [hzero]; decide) (attesterMultiRevokeLengthGuardJoinJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨206⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨207⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨236⟩ (by attester_decode_at v, ⟨208⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨211⟩, 0x57, .JUMPI)
      (by rw [hzero]; decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨212⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨214⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨215⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨220⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨222⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨223⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 attesterRequireSelectorMem (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨224⟩, 0x52, .MSTORE)
      mem_cost (by
        unfold attesterRequireSelectorMem
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨225⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨227⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨228⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by attester_decode_at v, ⟨230⟩, 0x51, .MLOAD)
      mem_cost attesterRequireSelectorMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨231⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨232⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨233⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨234⟩, 0x90, .SWAP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨235⟩, 0xfd, .REVERT)
      mem_cost (by evm_ov)]

theorem attesterX_multiRevokeLengthMismatchReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hneq :
      UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd192⟩ := hreach
  exact evm_run rd192 with [
    raw jumpdest (by attester_decode_at v, ⟨192⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨193⟩, 0x82, .DUP3) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨194⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨195⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨196⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨206⟩ (by attester_decode_at v, ⟨197⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨200⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨201⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨202⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨203⟩, 0x82, .DUP3) (by evm_ov),
    raw eq (by attester_decode_at v, ⟨204⟩, 0x14, .EQ) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨205⟩, 0x15, .ISZERO) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨206⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨207⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨236⟩ (by attester_decode_at v, ⟨208⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨211⟩, 0x57, .JUMPI)
      (by rw [hneq]; decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨212⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨214⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨215⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨220⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨222⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨223⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 attesterRequireSelectorMem (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨224⟩, 0x52, .MSTORE)
      mem_cost (by
        unfold attesterRequireSelectorMem
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨225⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨227⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨228⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by attester_decode_at v, ⟨230⟩, 0x51, .MLOAD)
      mem_cost attesterRequireSelectorMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨231⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨232⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨233⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨234⟩, 0x90, .SWAP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨235⟩, 0xfd, .REVERT)
      mem_cost (by evm_ov)]

theorem attesterX_multiRevokeLengthGuardOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (heq :
      UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨236⟩ : UInt256)
      [attesterFirstArrayLengthWord I, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd192⟩ := hreach
  exact ⟨_, _, evm_run rd192 with [
    raw jumpdest (by attester_decode_at v, ⟨192⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨193⟩, 0x82, .DUP3) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨194⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨195⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨196⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨206⟩ (by attester_decode_at v, ⟨197⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨200⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨201⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨202⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨203⟩, 0x82, .DUP3) (by evm_ov),
    raw eq (by attester_decode_at v, ⟨204⟩, 0x14, .EQ) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨205⟩, 0x15, .ISZERO) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨206⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨207⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨236⟩ (by attester_decode_at v, ⟨208⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨211⟩, 0x57, .JUMPI)
      (by rw [heq]; decide) (attesterMultiRevokeLengthGuardOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeLengthGuardOk_of_lengths {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables) {schemas schemaUids : List Value}
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hSchemasLen :
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hSchemaUidsLen :
      schemaUids.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hnonzero : schemas.length ≠ 0)
    (heqLen : schemas.length = schemaUids.length)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨192⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨236⟩ : UInt256)
      [attesterFirstArrayLengthWord I, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hrawFirstNe :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hrawZero
    exact hnonzero (by omega)
  have hrawEq :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    omega
  have hnonzeroEvm :=
    attesterFirstArrayLengthWord_isZero_of_nat_ne_zero (I := I) hoff0Max hrawFirstNe
  have heqEvm :=
    attesterArrayLengthWords_eq_one_of_nat_eq (I := I) hoff0Max hoff1Max hrawEq
  exact attesterX_multiRevokeLengthGuardOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) v hnonzeroEvm heqEvm hreach

theorem attesterX_multiRevokeAllocLengthMaxOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨236⟩ : UInt256)
      [attesterFirstArrayLengthWord I, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨261⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨0⟩, attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd236⟩ := hreach
  have hgt :
      UInt256.gt (attesterFirstArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0Max, hmaxToNat]
    exact Nat.le_of_not_gt hlen0Max
  exact ⟨_, _, evm_run rd236 with [
    raw jumpdest (by attester_decode_at v, ⟨236⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨237⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨238⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨239⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨241⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨243⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨245⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨246⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨247⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨248⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨249⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨261⟩ (by attester_decode_at v, ⟨250⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨253⟩, 0x57, .JUMPI)
      (by
        rw [hgt]
        decide)
      (attesterMultiRevokeAllocLengthMaxOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeOuterArrayInitEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨261⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨0⟩, attesterFirstArrayLengthWord I,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨291⟩ : UInt256)
      [((⟨32⟩ : UInt256) + ⟨128⟩), attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
        attesterFirstArrayLengthWord I, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨97⟩, solcSelectorWord I]
      (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd261⟩ := hreach
  exact ⟨_, _, evm_run rd261 with [
    raw jumpdest (by attester_decode_at v, ⟨261⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨262⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨264⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨265⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨266⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨267⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore 6 (attesterMultiOuterArrayLenMem I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨268⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨269⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨270⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨272⟩, 0x02, .MUL) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨273⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨275⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨276⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨277⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨278⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore 0 (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨280⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨281⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨282⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨330⟩ (by attester_decode_at v, ⟨283⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨286⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨287⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨288⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨290⟩, 0x01, .ADD) (by evm_ov)]⟩

theorem attesterX_multiAttestDecodedToBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨113⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨828⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd113⟩ := hreach
  exact ⟨_, _, evm_run rd113 with [
    raw jumpdest (by attester_decode_at v, ⟨113⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨828⟩ (by attester_decode_at v, ⟨114⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨117⟩, 0x56, .JUMP)
      (attesterMultiAttestBodyJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestLengthZeroReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨828⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd828⟩ := hreach
  exact evm_run rd828 with [
    raw jumpdest (by attester_decode_at v, ⟨828⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨829⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨831⟩, 0x83, .DUP4) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨832⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨833⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨834⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨844⟩ (by attester_decode_at v, ⟨835⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨838⟩, 0x57, .JUMPI)
      (by rw [hzero]; decide) (attesterMultiAttestLengthGuardJoinJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨844⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨845⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨874⟩ (by attester_decode_at v, ⟨846⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨849⟩, 0x57, .JUMPI)
      (by rw [hzero]; decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨850⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨852⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨853⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨858⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨860⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨861⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 attesterRequireSelectorMem (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨862⟩, 0x52, .MSTORE)
      mem_cost (by
        unfold attesterRequireSelectorMem
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨863⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨865⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨866⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by attester_decode_at v, ⟨868⟩, 0x51, .MLOAD)
      mem_cost attesterRequireSelectorMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨869⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨870⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨871⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨872⟩, 0x90, .SWAP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨873⟩, 0xfd, .REVERT)
      mem_cost (by evm_ov)]

theorem attesterX_multiAttestLengthMismatchReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hneq :
      UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨828⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd828⟩ := hreach
  exact evm_run rd828 with [
    raw jumpdest (by attester_decode_at v, ⟨828⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨829⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨831⟩, 0x83, .DUP4) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨832⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨833⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨834⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨844⟩ (by attester_decode_at v, ⟨835⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨838⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨839⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨840⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨841⟩, 0x83, .DUP4) (by evm_ov),
    raw eq (by attester_decode_at v, ⟨842⟩, 0x14, .EQ) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨843⟩, 0x15, .ISZERO) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨844⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨845⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨874⟩ (by attester_decode_at v, ⟨846⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨849⟩, 0x57, .JUMPI)
      (by rw [hneq]; decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨850⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨852⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push4 ⟨3036299187⟩ (by attester_decode_at v, ⟨853⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨858⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨860⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨861⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 attesterRequireSelectorMem (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨862⟩, 0x52, .MSTORE)
      mem_cost (by
        unfold attesterRequireSelectorMem
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨863⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨865⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨866⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by attester_decode_at v, ⟨868⟩, 0x51, .MLOAD)
      mem_cost attesterRequireSelectorMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨869⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨870⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨871⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨872⟩, 0x90, .SWAP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨873⟩, 0xfd, .REVERT)
      mem_cost (by evm_ov)]

theorem attesterX_multiAttestLengthGuardOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (heq :
      UInt256.eq (attesterSecondArrayLengthWord I) (attesterFirstArrayLengthWord I) = ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨828⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨874⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨96⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd828⟩ := hreach
  exact ⟨_, _, evm_run rd828 with [
    raw jumpdest (by attester_decode_at v, ⟨828⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨829⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨831⟩, 0x83, .DUP4) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨832⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨833⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨834⟩, 0x80, .DUP1) (by evm_ov),
    raw push2 ⟨844⟩ (by attester_decode_at v, ⟨835⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨838⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨839⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨840⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨841⟩, 0x83, .DUP4) (by evm_ov),
    raw eq (by attester_decode_at v, ⟨842⟩, 0x14, .EQ) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨843⟩, 0x15, .ISZERO) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨844⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨845⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨874⟩ (by attester_decode_at v, ⟨846⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨849⟩, 0x57, .JUMPI)
      (by rw [heq]; decide) (attesterMultiAttestLengthGuardOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestLengthGuardOk_of_lengths {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables) {schemas schemaInputs : List Value}
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hoff1Max : ¬ solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hSchemasLen :
      schemas.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hSchemaInputsLen :
      schemaInputs.length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hnonzero : schemas.length ≠ 0)
    (heqLen : schemas.length = schemaInputs.length)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨828⟩ : UInt256)
      [attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨874⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨96⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hrawFirstNe :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0 := by
    intro hrawZero
    exact hnonzero (by omega)
  have hrawEq :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    omega
  have hnonzeroEvm :=
    attesterFirstArrayLengthWord_isZero_of_nat_ne_zero (I := I) hoff0Max hrawFirstNe
  have heqEvm :=
    attesterArrayLengthWords_eq_one_of_nat_eq (I := I) hoff0Max hoff1Max hrawEq
  exact attesterX_multiAttestLengthGuardOk
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) v hnonzeroEvm heqEvm hreach

theorem attesterX_multiAttestAllocLengthMaxOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hoff0Max : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlen0Max : ¬ solcMaxU64 <
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨874⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨96⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨899⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨0⟩, attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd874⟩ := hreach
  have hgt :
      UInt256.gt (attesterFirstArrayLengthWord I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    have hmaxToNat :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩).toNat =
          solcMaxU64 := by
      native_decide
    rw [attesterFirstArrayLengthWord_toNat (I := I) hoff0Max, hmaxToNat]
    exact Nat.le_of_not_gt hlen0Max
  exact ⟨_, _, evm_run rd874 with [
    raw jumpdest (by attester_decode_at v, ⟨874⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨875⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨876⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨877⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨879⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨881⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨883⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨884⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨885⟩, 0x81, .DUP2) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨886⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨887⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨899⟩ (by attester_decode_at v, ⟨888⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨891⟩, 0x57, .JUMPI)
      (by
        rw [hgt]
        decide)
      (attesterMultiAttestAllocLengthMaxOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiAttestOuterArrayInitEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hnonzero : UInt256.isZero (attesterFirstArrayLengthWord I) = ⟨0⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨899⟩ : UInt256)
      [attesterFirstArrayLengthWord I, ⟨0⟩, attesterFirstArrayLengthWord I, ⟨96⟩,
        attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨929⟩ : UInt256)
      [((⟨32⟩ : UInt256) + ⟨128⟩), attesterFirstArrayLengthWord I, ⟨128⟩, ⟨0⟩,
        attesterFirstArrayLengthWord I, ⟨96⟩, attesterSecondArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 36)) + ⟨32⟩,
        attesterFirstArrayLengthWord I,
        (UInt256.add ⟨4⟩ (calldataWord I.calldata 4)) + ⟨32⟩,
        ⟨118⟩, solcSelectorWord I]
      (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd899⟩ := hreach
  exact ⟨_, _, evm_run rd899 with [
    raw jumpdest (by attester_decode_at v, ⟨899⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨900⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by attester_decode_at v, ⟨902⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨903⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨904⟩, 0x80, .DUP1) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨905⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore 6 (attesterMultiOuterArrayLenMem I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨906⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨907⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨908⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨910⟩, 0x02, .MUL) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨911⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨913⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨914⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨915⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨916⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore 0 (attesterMultiOuterArrayAllocMem I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨918⟩, 0x52, .MSTORE)
      mem_cost (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨919⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨920⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨968⟩ (by attester_decode_at v, ⟨921⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨924⟩, 0x57, .JUMPI)
      (by rw [hnonzero]) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨925⟩, 0x81, .DUP2) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨926⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨928⟩, 0x01, .ADD) (by evm_ov)]⟩

end Benchmarks.EAS.Attester
