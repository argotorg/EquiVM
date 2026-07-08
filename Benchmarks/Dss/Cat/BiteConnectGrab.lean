import Benchmarks.Dss.Cat.BiteTrace
import Benchmarks.Dss.Cat.BiteCallGrab

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-! ## STEP 1 — the 196-byte `grab` calldata window read at the free pointer `p` -/

theorem catBiteGrabCalldataMemP_read_window
    (p ilk urn thisW vowRaw dink dart : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size) :
    (catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding p.toNat 196 =
      vatGrabSelector ++ ilk.toByteArray ++ (UInt256.land biteAddrMaskWord urn).toByteArray
        ++ thisW.toByteArray ++ (UInt256.land biteAddrMaskWord vowRaw).toByteArray
        ++ (UInt256.sub ⟨0⟩ dink).toByteArray ++ (UInt256.sub ⟨0⟩ dart).toByteArray := by
  have e4 : (p + ⟨4⟩).toNat = p.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e36 : (p + ⟨36⟩).toNat = p.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e68 : (p + ⟨68⟩).toNat = p.toNat + 68 := by
    rw [uadd_toNat, show (⟨68⟩ : UInt256).toNat = 68 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e100 : (p + ⟨100⟩).toNat = p.toNat + 100 := by
    rw [uadd_toNat, show (⟨100⟩ : UInt256).toNat = 100 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e132 : (p + ⟨132⟩).toNat = p.toNat + 132 := by
    rw [uadd_toNat, show (⟨132⟩ : UInt256).toNat = 132 from by decide, Nat.mod_eq_of_lt (by omega)]
  have e164 : (p + ⟨164⟩).toNat = p.toNat + 164 := by
    rw [uadd_toNat, show (⟨164⟩ : UInt256).toNat = 164 from by decide, Nat.mod_eq_of_lt (by omega)]
  have hsSel := catBiteGrabSelMemP_size p hpmem
  have hsIlk := catBiteGrabIlkMemP_size p ilk hpmem hpsz
  have hsUrn := catBiteGrabUrnMemP_size p ilk urn hpmem hpsz
  have hsThis := catBiteGrabThisMemP_size p ilk urn thisW hpmem hpsz
  have hsVow := catBiteGrabVowMemP_size p ilk urn thisW vowRaw hpmem hpsz
  have hsDink := catBiteGrabDinkMemP_size p ilk urn thisW vowRaw dink hpmem hpsz
  have hsCall := catBiteGrabCalldataMemP_size p ilk urn thisW vowRaw dink dart hpmem hpsz
  set final := catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem with hfinal
  have hfinalSize : p.toNat + 196 ≤ final.size := by omega
  -- selector [p, p+4)
  have hSel : final.readWithPadding p.toNat 4 = vatGrabSelector := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabVowMemP
    rw [write32_read_below_len _ _ (p + ⟨100⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabThisMemP
    rw [write32_read_below_len _ _ (p + ⟨68⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabUrnMemP
    rw [write32_read_below_len _ _ (p + ⟨36⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabIlkMemP
    rw [write32_read_below_len _ _ (p + ⟨4⟩).toNat p.toNat 4 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabSelMemP
    rw [write32_read_prefix_len _ _ p.toNat 4 (by rw [toByteArray_size]) hpmem (by norm_num)
      (by norm_num) (by norm_num)]
    native_decide
  -- ilk [p+4, p+36)
  have hIlk : final.readWithPadding (p.toNat + 4) 32 = ilk.toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabVowMemP
    rw [write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabThisMemP
    rw [write32_read_below_len _ _ (p + ⟨68⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabUrnMemP
    rw [write32_read_below_len _ _ (p + ⟨36⟩).toNat (p.toNat + 4) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabIlkMemP
    rw [e4, toByteArray_write32_read_back _ ilk (p.toNat + 4) (by omega)]
  -- urn [p+36, p+68)
  have hUrn : final.readWithPadding (p.toNat + 36) 32 =
      (UInt256.land biteAddrMaskWord urn).toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabVowMemP
    rw [write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabThisMemP
    rw [write32_read_below_len _ _ (p + ⟨68⟩).toNat (p.toNat + 36) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabUrnMemP
    rw [e36, toByteArray_write32_read_back _ (UInt256.land biteAddrMaskWord urn) (p.toNat + 36)
      (by omega)]
  -- this [p+68, p+100)
  have hThis : final.readWithPadding (p.toNat + 68) 32 = thisW.toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat (p.toNat + 68) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 68) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabVowMemP
    rw [write32_read_below_len _ _ (p + ⟨100⟩).toNat (p.toNat + 68) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabThisMemP
    rw [e68, toByteArray_write32_read_back _ thisW (p.toNat + 68) (by omega)]
  -- vow [p+100, p+132)
  have hVow : final.readWithPadding (p.toNat + 100) 32 =
      (UInt256.land biteAddrMaskWord vowRaw).toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat (p.toNat + 100) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [write32_read_below_len _ _ (p + ⟨132⟩).toNat (p.toNat + 100) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabVowMemP
    rw [e100, toByteArray_write32_read_back _ (UInt256.land biteAddrMaskWord vowRaw) (p.toNat + 100)
      (by omega)]
  -- dink [p+132, p+164)
  have hDink : final.readWithPadding (p.toNat + 132) 32 = (UInt256.sub ⟨0⟩ dink).toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [write32_read_below_len _ _ (p + ⟨164⟩).toNat (p.toNat + 132) 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega) (by norm_num) (by norm_num)]
    unfold catBiteGrabDinkMemP
    rw [e132, toByteArray_write32_read_back _ (UInt256.sub ⟨0⟩ dink) (p.toNat + 132) (by omega)]
  -- dart [p+164, p+196)
  have hDart : final.readWithPadding (p.toNat + 164) 32 = (UInt256.sub ⟨0⟩ dart).toByteArray := by
    rw [hfinal]
    unfold catBiteGrabCalldataMemP
    rw [e164, toByteArray_write32_read_back _ (UInt256.sub ⟨0⟩ dart) (p.toNat + 164) (by omega)]
  -- assemble
  rw [readWithPadding_eq_extract' final p.toNat 196 (by norm_num) (by norm_num)
    (by omega)]
  have hSelExt : final.extract p.toNat (p.toNat + 4) = vatGrabSelector := by
    rw [← readWithPadding_eq_extract' final p.toNat 4 (by norm_num) (by norm_num) (by omega)]
    exact hSel
  have hIlkExt : final.extract (p.toNat + 4) (p.toNat + 36) = ilk.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 4) 32 (by norm_num) (by norm_num) (by omega)]
    exact hIlk
  have hUrnExt : final.extract (p.toNat + 36) (p.toNat + 68) =
      (UInt256.land biteAddrMaskWord urn).toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 36) 32 (by norm_num) (by norm_num) (by omega)]
    exact hUrn
  have hThisExt : final.extract (p.toNat + 68) (p.toNat + 100) = thisW.toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 68) 32 (by norm_num) (by norm_num) (by omega)]
    exact hThis
  have hVowExt : final.extract (p.toNat + 100) (p.toNat + 132) =
      (UInt256.land biteAddrMaskWord vowRaw).toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 100) 32 (by norm_num) (by norm_num) (by omega)]
    exact hVow
  have hDinkExt : final.extract (p.toNat + 132) (p.toNat + 164) =
      (UInt256.sub ⟨0⟩ dink).toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 132) 32 (by norm_num) (by norm_num) (by omega)]
    exact hDink
  have hDartExt : final.extract (p.toNat + 164) (p.toNat + 196) =
      (UInt256.sub ⟨0⟩ dart).toByteArray := by
    rw [← readWithPadding_eq_extract' final (p.toNat + 164) 32 (by norm_num) (by norm_num) (by omega)]
    exact hDart
  have hsplit : final.extract p.toNat (p.toNat + 196) =
      final.extract p.toNat (p.toNat + 4) ++ final.extract (p.toNat + 4) (p.toNat + 36) ++
        final.extract (p.toNat + 36) (p.toNat + 68) ++ final.extract (p.toNat + 68) (p.toNat + 100) ++
        final.extract (p.toNat + 100) (p.toNat + 132) ++ final.extract (p.toNat + 132) (p.toNat + 164)
        ++ final.extract (p.toNat + 164) (p.toNat + 196) := by
    rw [show final.extract p.toNat (p.toNat + 196) =
        final.extract p.toNat (p.toNat + 4) ++ final.extract (p.toNat + 4) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 4) (p.toNat + 196) =
        final.extract (p.toNat + 4) (p.toNat + 36) ++ final.extract (p.toNat + 36) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 36) (p.toNat + 196) =
        final.extract (p.toNat + 36) (p.toNat + 68) ++ final.extract (p.toNat + 68) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 68) (p.toNat + 196) =
        final.extract (p.toNat + 68) (p.toNat + 100) ++ final.extract (p.toNat + 100) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 100) (p.toNat + 196) =
        final.extract (p.toNat + 100) (p.toNat + 132) ++ final.extract (p.toNat + 132) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    rw [show final.extract (p.toNat + 132) (p.toNat + 196) =
        final.extract (p.toNat + 132) (p.toNat + 164) ++ final.extract (p.toNat + 164) (p.toNat + 196) by
      rw [ByteArray.extract_append_extract]; congr 1 <;> omega]
    simp
  rw [hsplit, hSelExt, hIlkExt, hUrnExt, hThisExt, hVowExt, hDinkExt, hDartExt]

/-! ## STEP 2 — the ABI-encoding coupling for `vat.grab(...)` -/

/-- The signed `int256` negative encoding: `-int256(x)` two's-complements to `0 - x`. -/
theorem grab_neg_int_word (x : UInt256) :
    EVM.wordOfInt (-(Int.ofNat x.toNat)) = UInt256.sub ⟨0⟩ x := by
  have hlt : x.toNat < UInt256.size := x.val.isLt
  rcases Nat.eq_zero_or_pos x.toNat with h0 | hpos
  · have hx : x = ⟨0⟩ := u256_inj (by rw [h0]; rfl)
    subst hx
    decide
  · apply u256_inj
    rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := x)
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; exact hpos),
      show (⟨0⟩ : UInt256).toNat = 0 from rfl]
    have hneg : -(Int.ofNat x.toNat) < 0 := by
      show -(x.toNat : ℤ) < 0; omega
    have hAbs : (-(Int.ofNat x.toNat)).natAbs = x.toNat := by
      show (-(x.toNat : ℤ)).natAbs = x.toNat; simp
    unfold EVM.wordOfInt
    rw [if_pos hneg, hAbs, show EVM.wordModulus = UInt256.size from rfl, Nat.mod_eq_of_lt hlt,
      if_neg (by omega : ¬ x.toNat = 0),
      show EVM.word (UInt256.size - x.toNat) = UInt256.ofNat (UInt256.size - x.toNat) from rfl,
      ulit_toNat' (UInt256.size - x.toNat) (by omega)]
    omega

theorem catBiteGrabEncode_eq (p ilk urn thisW vowRaw dink dart : UInt256) {mem : ByteArray}
    (hp96 : 96 ≤ p.toNat) (hpmem : p.toNat ≤ mem.size) (hpsz : p.toNat + 196 < UInt256.size)
    (hthisCanon : thisW.toNat < EVM.addressModulus)
    (hdink : dink.toNat ≤ 2 ^ 255) (hdart : dart.toNat ≤ 2 ^ 255) :
    config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (EVM.Word.toBytesBE ilk),
       .address (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat),
       .address (AccountAddress.ofNat thisW.toNat),
       .address (AccountAddress.ofNat (UInt256.land biteAddrMaskWord vowRaw).toNat),
       .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))] =
      some ((catBiteGrabCalldataMemP p ilk urn thisW vowRaw dink dart mem).readWithPadding p.toNat 196) := by
  rw [catBiteGrabCalldataMemP_read_window p ilk urn thisW vowRaw dink dart hp96 hpmem hpsz]
  -- bytes32 ilk field
  have hilkLen : (EVM.Word.toBytesBE ilk).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size ilk
  -- address masks are canonical
  have hmaskEq : biteAddrMaskWord = solcAddrMask := by native_decide
  have hurnCanon : (UInt256.land biteAddrMaskWord urn).toNat < EVM.addressModulus := by
    rw [hmaskEq, u256_land_comm]; exact solcAddrMask_result_canonical urn
  have hvowCanon : (UInt256.land biteAddrMaskWord vowRaw).toNat < EVM.addressModulus := by
    rw [hmaskEq, u256_land_comm]; exact solcAddrMask_result_canonical vowRaw
  have hurnWord : EVM.word ↑(AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat) =
      UInt256.land biteAddrMaskWord urn := by
    have haddrVal : (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat).val =
        (UInt256.land biteAddrMaskWord urn).toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using hurnCanon)
    change UInt256.ofNat (AccountAddress.ofNat (UInt256.land biteAddrMaskWord urn).toNat).val =
      UInt256.land biteAddrMaskWord urn
    rw [haddrVal]; exact u256_ofNat_toNat _
  have hthisWord : EVM.word ↑(AccountAddress.ofNat thisW.toNat) = thisW := by
    have haddrVal : (AccountAddress.ofNat thisW.toNat).val = thisW.toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using hthisCanon)
    change UInt256.ofNat (AccountAddress.ofNat thisW.toNat).val = thisW
    rw [haddrVal]; exact u256_ofNat_toNat _
  have hvowWord : EVM.word ↑(AccountAddress.ofNat (UInt256.land biteAddrMaskWord vowRaw).toNat) =
      UInt256.land biteAddrMaskWord vowRaw := by
    have haddrVal : (AccountAddress.ofNat (UInt256.land biteAddrMaskWord vowRaw).toNat).val =
        (UInt256.land biteAddrMaskWord vowRaw).toNat := by
      unfold AccountAddress.ofNat
      simp only [Fin.val_ofNat]
      exact Nat.mod_eq_of_lt (by simpa [AccountAddress.size] using hvowCanon)
    change UInt256.ofNat (AccountAddress.ofNat (UInt256.land biteAddrMaskWord vowRaw).toNat).val =
      UInt256.land biteAddrMaskWord vowRaw
    rw [haddrVal]; exact u256_ofNat_toNat _
  -- int256 negative bounds (in the shape simp normalizes the sint range-check to)
  have htp : EVM.twoPow 255 = 2 ^ 255 := rfl
  have htpPos : 0 < (2 : ℕ) ^ 255 := by positivity
  have htpPosZ : (0 : ℤ) < (EVM.twoPow 255 : ℤ) := by rw [htp]; exact_mod_cast htpPos
  have hdinkNat : dink.toNat ≤ EVM.twoPow 255 := by rw [htp]; exact hdink
  have hdartNat : dart.toNat ≤ EVM.twoPow 255 := by rw [htp]; exact hdart
  have hdinkHi2 : -(dink.toNat : ℤ) < (EVM.twoPow 255 : ℤ) := by
    have h2 : (0 : ℤ) ≤ (dink.toNat : ℤ) := Nat.cast_nonneg _
    omega
  have hdartHi2 : -(dart.toNat : ℤ) < (EVM.twoPow 255 : ℤ) := by
    have h2 : (0 : ℤ) ≤ (dart.toNat : ℤ) := Nat.cast_nonneg _
    omega
  have hdinkW : EVM.wordOfInt (-(dink.toNat : ℤ)) = UInt256.sub ⟨0⟩ dink := grab_neg_int_word dink
  have hdartW : EVM.wordOfInt (-(dart.toNat : ℤ)) = UInt256.sub ⟨0⟩ dart := grab_neg_int_word dart
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256, int256Int,
    vatGrabSelector, selectorBytes, hilkLen, hurnWord, hthisWord, hvowWord,
    hdinkNat, hdartNat, hdinkHi2, hdartHi2, hdinkW, hdartW, ABI.zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

end Benchmarks.Dss.Cat
