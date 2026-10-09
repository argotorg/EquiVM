import Benchmarks.CompoundIII.Comet.Solc0815Decode
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

abbrev absorbArrayOffset (cd : ByteArray) : Nat := (calldataWord cd 36).toNat

abbrev absorbArrayLength (cd : ByteArray) : Nat :=
  (calldataWord cd (4 + absorbArrayOffset cd)).toNat

abbrev AbsorbCalldataValid (cd : ByteArray) : Prop :=
  68 ≤ cd.size ∧ cd.size < 2^255 ∧
    (calldataWord cd 4).toNat < EVM.addressModulus ∧
    absorbArrayOffset cd ≤ solcMaxU64 ∧ absorbArrayOffset cd + 36 ≤ cd.size ∧
    absorbArrayLength cd ≤ solcMaxU64 ∧
    absorbArrayOffset cd + 36 + 32 * absorbArrayLength cd ≤ cd.size

def absorbCalldataArgs (cd : ByteArray) (accounts : List Value) : Store :=
  ((∅ : Store).insert "absorber" (.address (AccountAddress.ofNat
    (calldataWord cd 4).toNat))).insert "accounts" (.array accounts)

theorem solc0815_decodeCalldata_addressArray_prefix {cd : ByteArray} {x y : Ident}
    (hhead : 68 ≤ cd.size) (hhi : cd.size < 2^255) :
    decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd =
      if (calldataWord cd 4).toNat < EVM.addressModulus then
        if solcMaxU64 < absorbArrayOffset cd then none
        else (decodeABIValue? (.dynamicArray (.elem .address)) (cd.toList.drop 4)
          (absorbArrayOffset cd) .solc0815).map fun (value, _) ↦
            ((∅ : Store).insert x (.address (AccountAddress.ofNat
              (calldataWord cd 4).toNat))).insert y value
      else none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]; omega
  have hw4 : bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq_any cd 4 (by omega)
  have haddr : decodeABIValue? (.elem .address) (cd.toList.drop 4) 0 .solc0815 =
      if (calldataWord cd 4).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd 4).toNat), 32) else none := by
    simp only [decodeABIValue?, readWord?, readBytes?, List.drop_zero, htake, if_true,
      bind, Option.bind, hw4, decodeABIWord?, UInt256.toNat]
    split_ifs <;> rfl
  have hoffRead := readNat_drop4_at_eq_calldataWord (cd := cd) 32 hhead
  have hshort : ¬ cd.toList.length < 4 := by omega
  have hbig : cd.toList.length < 2^255 := by omega
  have hargsBig : cd.toList.length - 4 < 2^255 := by omega
  have hargsShort : ¬ cd.toList.length - 4 < 64 := by omega
  simp only [decodeCalldataWithMode, decodeCalldata, hshort, if_false,
    List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.true_or,
    if_true, true_and, not_le.mpr hbig, List.isEmpty_cons,
    Bool.false_eq_true, false_and, solcTotalSizeDynamicGuard, List.length_drop,
    not_le.mpr hargsBig, decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [.elem .address, .dynamicArray (.elem .address)] = some 64 by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?]]
  simp only [bind, Option.bind, hargsShort, if_false]
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus <;>
    by_cases hoff : solcMaxU64 < absorbArrayOffset cd <;>
    cases harray : decodeABIValue? (.dynamicArray (.elem .address)) (cd.toList.drop 4)
      (absorbArrayOffset cd) .solc0815 <;>
    simp [decodeABIValues?, isDynamicABIType, staticABIEncodedSize?, haddr, hc, hoff,
      hoffRead, solcMaxLen, harray, decodeCalldata.insertValues]

-- LIBRARY CANDIDATE (Reasoning/ABI): a calldata (address, address[]) tuple in solc 0.8.15.
theorem solc0815_decodeCalldata_addressArray_ok {cd : ByteArray} {x y : Ident}
    {values : List Value} {endOffset : Nat}
    (hhead : 68 ≤ cd.size) (hhi : cd.size < 2^255)
    (hc : (calldataWord cd 4).toNat < EVM.addressModulus)
    (hoff : absorbArrayOffset cd ≤ solcMaxU64)
    (hword : absorbArrayOffset cd + 36 ≤ cd.size)
    (hn : absorbArrayLength cd ≤ solcMaxU64)
    (hvalues : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (values, endOffset)) :
    decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd =
      some (((∅ : Store).insert x (.address (AccountAddress.ofNat
        (calldataWord cd 4).toNat))).insert y (.array values)) := by
  have hnRead := readNat_drop4_at_eq_calldataWord (cd := cd) (absorbArrayOffset cd)
    (by omega)
  have harray := solc0815_decodeAddressArray_ok hnRead hn hvalues
  rw [solc0815_decodeCalldata_addressArray_prefix hhead hhi, if_pos hc,
    if_neg (Nat.not_lt.mpr hoff), harray]
  rfl

theorem solc0815_decodeCalldata_addressArray_none_huge {cd : ByteArray} {x y : Ident}
    (hhi : 2^255 ≤ cd.size) :
    decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change decodeCalldata [x, y] [.elem .address, .dynamicArray (.elem .address)] cd .solc0815 = _
  unfold decodeCalldata
  rw [if_neg (by omega : ¬ cd.toList.length < 4)]
  rw [if_pos ⟨rfl, by omega⟩]

theorem solc0815_decodeCalldata_addressArray_none_short {cd : ByteArray} {x y : Ident}
    (hhead : cd.size < 68) :
    decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  change decodeCalldata [x, y] [.elem .address, .dynamicArray (.elem .address)] cd .solc0815 = _
  unfold decodeCalldata
  by_cases hshort : cd.toList.length < 4
  · rw [if_pos hshort]
  · rw [if_neg hshort]
    rw [if_neg (by rintro ⟨_, h⟩; omega)]
    simp only
    rw [if_neg (by rintro ⟨_, h⟩; rw [List.length_drop, hlen] at h; omega)]
    simp only [solcTotalSizeDynamicGuard, Bool.false_eq_true, false_and, if_false,
      decodeCalldata.decodeArgs]
    rw [show abiTupleHeadSize? [.elem .address, .dynamicArray (.elem .address)] = some 64 by
      simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?]]
    simp only [bind, Option.bind]
    rw [if_pos (by rw [List.length_drop, hlen]; omega)]

theorem solc0815_decodeCalldata_addressArray_valid {cd : ByteArray} {x y : Ident} {args : Store}
    (h : decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd = some args) :
    AbsorbCalldataValid cd := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hhead : 68 ≤ cd.size := by
    by_contra hhead
    rw [solc0815_decodeCalldata_addressArray_none_short (by omega)] at h
    cases h
  have hhi : cd.size < 2^255 := by
    by_contra hhi
    rw [solc0815_decodeCalldata_addressArray_none_huge (by omega)] at h
    cases h
  rw [solc0815_decodeCalldata_addressArray_prefix hhead hhi] at h
  by_cases hc : (calldataWord cd 4).toNat < EVM.addressModulus
  · rw [if_pos hc] at h
    by_cases hoff : solcMaxU64 < absorbArrayOffset cd
    · rw [if_pos hoff] at h
      cases h
    · rw [if_neg hoff] at h
      cases ha : decodeABIValue? (.dynamicArray (.elem .address)) (cd.toList.drop 4)
          (absorbArrayOffset cd) .solc0815 with
      | none => simp [ha] at h
      | some result =>
          rw [decodeABIValue?] at ha
          cases hr : readNat? (cd.toList.drop 4) (absorbArrayOffset cd) with
          | none => simp [hr] at ha
          | some n =>
              have hword := readNat?_some_length hr
              have hword' : absorbArrayOffset cd + 36 ≤ cd.size := by
                rw [List.length_drop, hlen] at hword
                omega
              have hnRead := readNat_drop4_at_eq_calldataWord (cd := cd)
                (absorbArrayOffset cd) (by omega)
              have hnEq : n = absorbArrayLength cd := Option.some.inj (hr.symm.trans hnRead)
              subst n
              by_cases hn : solcMaxU64 < absorbArrayLength cd
              · simp [hr, solcMaxLen, hn] at ha
              · cases hv : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd)
                    (cd.toList.drop 4) (absorbArrayOffset cd + 32) with
                | none => simp [hr, solcMaxLen, hn, hv] at ha
                | some values =>
                    obtain ⟨hend, hbound, _⟩ := solc0815_decodeAddressArrayElems_facts hword hv
                    refine ⟨hhead, hhi, hc, by omega, hword', by omega, ?_⟩
                    rw [hend, List.length_drop, hlen] at hbound
                    omega
  · rw [if_neg hc] at h
    cases h

theorem absorbCalldata_decode_valid {cd : ByteArray} (h : AbsorbCalldataValid cd) :
    ∃ accounts endOffset,
      Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
        (absorbArrayOffset cd + 32) = some (accounts, endOffset) ∧
      accounts.length = absorbArrayLength cd ∧
      decodeCalldataWithMode .solc0815 ["absorber", "accounts"]
        [.elem .address, .dynamicArray (.elem .address)] cd =
          some (absorbCalldataArgs cd accounts) := by
  rcases h with ⟨hhead, hhi, hc, hoff, hword, hn, hbound⟩
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨accounts, haccounts, hlength⟩ := solc0815_decodeAddressArrayElems_exists
    (bytes := cd.toList.drop 4) (start := absorbArrayOffset cd + 32)
    (n := absorbArrayLength cd) (by rw [List.length_drop, hlen]; omega)
  exact ⟨accounts, _, haccounts, hlength,
    solc0815_decodeCalldata_addressArray_ok hhead hhi hc hoff hword hn haccounts⟩

theorem absorbCalldata_decode_invalid {cd : ByteArray} {x y : Ident}
    (h : ¬ AbsorbCalldataValid cd) :
    decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd = none := by
  cases hd : decodeCalldataWithMode .solc0815 [x, y]
      [.elem .address, .dynamicArray (.elem .address)] cd with
  | none => rfl
  | some args => exact False.elim (h (solc0815_decodeCalldata_addressArray_valid hd))

theorem absorbCalldata_account_index {cd : ByteArray} {accounts : List Value}
    {endOffset i : Nat}
    (h : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hi : i < absorbArrayLength cd) :
    evalIndex? (.array accounts) (.int (Int.ofNat i)) =
      if (calldataWord cd (absorbArrayOffset cd + 36 + 32 * i)).toNat < EVM.addressModulus
      then .ok (.address (AccountAddress.ofNat
        (calldataWord cd (absorbArrayOffset cd + 36 + 32 * i)).toNat)) else .revert := by
  obtain ⟨word, hread, hindex⟩ := solc0815_decodeAddressArrayElems_index h hlen hi
  have hsize : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hbound := readNat?_some_length hread
  have hword := readNat_drop4_at_eq_calldataWord (cd := cd)
    (absorbArrayOffset cd + 32 + 32 * i) (by
      rw [List.length_drop, hsize] at hbound
      omega)
  have heq := Option.some.inj (hread.symm.trans hword)
  rw [heq] at hindex
  rw [show 4 + (absorbArrayOffset cd + 32 + 32 * i) =
    absorbArrayOffset cd + 36 + 32 * i by omega] at hindex
  exact hindex

end Benchmarks.CompoundIII.Comet
