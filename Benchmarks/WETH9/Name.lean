import Benchmarks.WETH9.StringEncode

/-! # WETH9 `Name` refinement

`name()` is a public non-payable getter returning the dynamic string stored at slot 0.  The EVM
return encoder is proved in `StringReturn.lean`/`StringReturnLong2.lean` (empty/short/long); this
module connects those `RDret`s to the Solm `.return [.storage nameRef]` body via `returnEquiv`.
Shared header/word/slot-parametric encode machinery lives in `StringEncode.lean`. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.WETH9

/-! ## Solm-side `name()` storage read -/

/-- The evaled `name` storage reference. -/
def nameEvaledRef : EvaledStorageRef := { base := "name", steps := [] }

/-- The Solm `name()` body's `.storage nameRef` evaluates through the WETH9 total-decode string
    hook `weth9ReadBytesValue?`. -/
theorem weth9NameStorageRead {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
      (.storage nameRef)
    = storageValueResultToEval (weth9ReadBytesValue? storageLayoutRaw
        nameEvaledRef (initState cA gh bl σ σ₀ g A I)) := by
  rw [evalExpr?, resolveStorageRef?_ok (er := nameEvaledRef) (ty := .string)
    (by simp [nameRef])
    (by simp [evalStorageRef, nameRef, nameEvaledRef, EvalResult.bind, bind, pure])
    (by simp [storageTypeAt?, contract, storageDecls, nameEvaledRef])]
  simp only [bind, EvalResult.bind, readStorage?, config, storageLayout, weth9StorageLayout,
    weth9ReadValue?]

theorem weth9NameBaseSlotLen {cA gh bl σ σ₀ A I} {g : Sat256} :
    weth9BytesBaseSlotAndLength? storageLayoutRaw nameEvaledRef (initState cA gh bl σ σ₀ g A I) =
      .ok ((⟨0⟩ : UInt256), (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) := by
  unfold weth9BytesBaseSlotAndLength?
  simp only [nameEvaledRef, List.nil_append, storageLayoutRaw, bytesLikeLengthLoc,
    apply_ite StorageLoc.slot, ite_self, weth9Header, weth9DecodeBytesLengthHeader_stringLen]

/-- The `.bytes` value the Solm `name()` body returns: the decoded compact string. -/
theorem weth9NameReadValue {cA gh bl σ σ₀ A I} {g : Sat256} :
    weth9ReadBytesValue? storageLayoutRaw nameEvaledRef (initState cA gh bl σ σ₀ g A I) =
      .ok (.bytes (if (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat < 32
        then (weth9StringSlotWord σ I ⟨0⟩).toByteArray.extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat
        else (readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) := by
  unfold weth9ReadBytesValue?
  rw [weth9NameBaseSlotLen]
  simp only [weth9Header]
  split <;> rfl

/-- The full Solm `name()` body `evalExpr?` result. -/
theorem weth9NameEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
      (.storage nameRef)
    = .ok (.bytes (if (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat < 32
        then (weth9StringSlotWord σ I ⟨0⟩).toByteArray.extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat
        else (readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) := by
  rw [weth9NameStorageRead, weth9NameReadValue]; rfl

/-! ## Long-case name-specific helpers (slot 0) -/

theorem weth9LongSlot_eq (σ : AccountMap) (I : ExecutionEnv) (k : ℕ) :
    (weth9LongGeneratedLoopState σ I k).slot = solidityBytesDataSlot ⟨0⟩ k := by
  induction k with
  | zero =>
    show solidityBytesDataBaseSlot ⟨0⟩ = solidityBytesDataBaseSlot ⟨0⟩ + UInt256.ofNat 0
    rw [show (UInt256.ofNat 0 : UInt256) = ⟨0⟩ from rfl, uadd_zero_r]
  | succ k ih =>
    show (⟨1⟩ : UInt256) + (weth9LongGeneratedLoopState σ I k).slot = solidityBytesDataSlot ⟨0⟩ (k + 1)
    rw [ih]
    show (⟨1⟩ : UInt256) + (solidityBytesDataBaseSlot ⟨0⟩ + UInt256.ofNat k) =
      solidityBytesDataBaseSlot ⟨0⟩ + UInt256.ofNat (k + 1)
    exact uadd_ofNat_succ _ _

theorem read_eq_wordConcat {cA gh bl σ σ₀ A I} {g : Sat256} (n idx : ℕ) :
    readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ idx n =
      wordConcat (weth9LongDataWordAt σ I) idx n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih =>
    unfold readSolidityBytesDataWordsFrom
    rw [wordConcat_succ, ih (idx + 1), weth9LongStorageLoad, weth9LongDataWordAt, weth9LongSlot_eq]

theorem wcp_eq (σ : AccountMap) (I : ExecutionEnv)
    (hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat) :
    solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat =
      weth9LongWC σ I + 1 := by
  unfold solidityBytesDataWordCount weth9LongWC
  omega

/-- The trailing (masked) data word: the last storage word `extract`ed to its `s = len mod 32`
    significant bytes and zero-padded is exactly `weth9LongMaskWord` (both the full and partial cases). -/
theorem weth9LongLastWord (σ : AccountMap) (I : ExecutionEnv) (s : ℕ)
    (hs1 : 1 ≤ s) (hs32 : s ≤ 32)
    (hcase : (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩ ∧ s = 32) ∨
      ((UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))).toNat = s ∧ s ≤ 31)) :
    (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0 s ++
        (List.replicate (32 - s) 0).toByteArray =
      UInt256.toByteArray (weth9LongMaskWord σ I) := by
  rw [weth9LongMaskWord]
  rcases hcase with ⟨hcond, hs⟩ | ⟨hLtoNat, hs31⟩
  · rw [if_pos hcond, hs, Nat.sub_self, List.replicate_zero, List.toByteArray_nil,
      ByteArray.append_empty, toByteArray_extract_all]
  · have hcond : UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩ := by
      intro h; rw [h, show (⟨0⟩ : UInt256).toNat = 0 from rfl] at hLtoNat; omega
    rw [if_neg hcond, tailMask_toByteArray (weth9LongDataWordAt σ I (weth9LongWC σ I))
        (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)))
        (by rw [hLtoNat]; exact hs1) (by rw [hLtoNat]; exact hs31),
      hLtoNat, bytearray_append_list_eq]

/-- Long string (`len ≥ 32`): the decoded keccak-data bytes ABI-encode to `weth9LongStringAbi`. -/
theorem weth9NameEncode_long {cA gh bl σ σ₀ A I} {g : Sat256}
    (hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) ≠ ⟨0⟩)
    (hfit : 96 + 32 * weth9LongWC σ I < 2 ^ 64) :
    encodeReturnValue? stringTy (.bytes
      ((readSolidityBytesDataWordsFrom (initState cA gh bl σ σ₀ g A I) ⟨0⟩ 0
          (solidityBytesDataWordCount (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)).extract 0
        (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat)) = some (weth9LongStringAbi σ I) := by
  have hlen32 : 32 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
    have := weth9LongLen_ge32 hge31; omega
  have hpos : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by omega
  have hwc : weth9LongWC σ I = ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 1) / 32 := rfl
  rw [wcp_eq σ I hpos, read_eq_wordConcat, wordConcat_append_last, Nat.zero_add]
  have hAsize : (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I)).size =
      32 * weth9LongWC σ I := wordConcat_size _ _ _
  have hBsize : (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.size = 32 := toByteArray_size _
  have hle : 32 * weth9LongWC σ I ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by omega
  have hs32 : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I ≤ 32 := by omega
  have hs1 : 1 ≤ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I := by omega
  rw [extract_append_span _ _ 0 _ (Nat.zero_le _) (by rw [hAsize]; exact hle),
    byteArray_extract_self, hAsize]
  have hbsize : (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
      (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
        ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I)).size =
      (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat := by
    rw [ByteArray.size_append, hAsize, ByteArray.size_extract, hBsize]; omega
  have hcase : (UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩ ∧
        (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I = 32) ∨
      ((UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩))).toNat =
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I ∧
        (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I ≤ 31) := by
    by_cases hc : UInt256.land ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) = ⟨0⟩
    · refine Or.inl ⟨hc, ?_⟩
      have hm0 : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 = 0 := by
        rw [← land31_toNat_mod, hc]; rfl
      omega
    · refine Or.inr ⟨?_, ?_⟩
      · have hmne : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 ≠ 0 := by
          rw [← land31_toNat_mod]; intro h; exact hc (uint256_toNat_eq_zero h)
        rw [land31_toNat_mod]; omega
      · have hmne : (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat % 32 ≠ 0 := by
          rw [← land31_toNat_mod]; intro h; exact hc (uint256_toNat_eq_zero h)
        omega
  have e1 : (ABI.natBytes 32).toByteArray = UInt256.toByteArray ⟨32⟩ := by
    rw [natBytes_toByteArray]; rfl
  have e2 : (ABI.natBytes (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
        (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
          ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat -
            32 * weth9LongWC σ I)).size).toByteArray =
      UInt256.toByteArray (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)) := by
    rw [natBytes_toByteArray, hbsize, u256_ofNat_toNat]
  have e3 : (ABI.padRightToWord (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
        (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
          ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat -
            32 * weth9LongWC σ I)).toList).toByteArray =
      wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
        UInt256.toByteArray (weth9LongMaskWord σ I) := by
    have hpad : ABI.padRightToWord (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
          (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
            ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I)).toList =
        (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
          (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
            ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I)).toList ++
          List.replicate (32 - ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat -
            32 * weth9LongWC σ I)) 0 := by
      unfold ABI.padRightToWord ABI.zeroBytes
      rw [show (wordConcat (weth9LongDataWordAt σ I) 0 (weth9LongWC σ I) ++
            (weth9LongDataWordAt σ I (weth9LongWC σ I)).toByteArray.extract 0
              ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat -
                32 * weth9LongWC σ I)).toList.length =
          (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat from by
            rw [byteArray_toList_eq, Array.length_toList]; exact hbsize,
        show ABI.paddedSize (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat =
            32 * (weth9LongWC σ I + 1) from by unfold ABI.paddedSize; congr 1; omega]
      rw [show 32 * (weth9LongWC σ I + 1) - (weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat =
        32 - ((weth9StringLen (weth9StringSlotWord σ I ⟨0⟩)).toNat - 32 * weth9LongWC σ I) from by omega]
    rw [hpad, List.toByteArray_append, toList_toByteArray_roundtrip, ByteArray.append_assoc,
      weth9LongLastWord σ I _ hs1 hs32 hcase]
  rw [encode_string_bytes, weth9LongStringAbi, mk_toArray_eq, List.toByteArray_append,
    List.toByteArray_append, e1, e2, e3]

/-! ## Dispatch / decode -/

/-- `name()`'s selector (index 0) dispatches to `nameTransition`. -/
theorem weth9SelectorDispatchName {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 0)) :
    selectorDispatchMsg contract I.calldata = some nameTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 0 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes]
  native_decide

/-- `name()` has no parameters: its ABI decode yields the empty store. -/
theorem weth9Decode_name_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (nameTransition.params.map Param.name)
      (transitionSignature nameTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem weth9NameBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 0))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 0) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · -- string return: the Solm `.return [.storage nameRef]` body ABI-encodes to the EVM encoder's
    -- output (`StringReturnLong2.lean`); `weth9NameReturnSizeBound` handles the ≥2^64-byte regime.
    have hbody := nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
      (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (locals := ∅)
      (by simp only [initState]; exact hwv) weth9NameEval
    have hHbr : weth9StringSlotWord σ_solm I ⟨0⟩ = weth9StringSlotWord σ_evm I ⟨0⟩ :=
      (weth9StringSlotWord_bridge (I := I) hAccounts ⟨0⟩).symm
    by_cases hlen0 : weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩) = ⟨0⟩
    · -- EMPTY (len = 0)
      have hlen0' : (weth9StringLen (weth9StringSlotWord σ_solm I ⟨0⟩)).toNat = 0 := by
        rw [hHbr, hlen0]; rfl
      exact weth9ReEquivExecTransport hcode
        (weth9NameStringEmptyReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hlen0)
        (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
        (by rw [nameTransition]; exact hbody) rfl hAccounts
        (returnEquiv_of_encode (weth9EncodeEmpty _ (by
          simp only [hlen0', show (0 : Nat) < 32 from by norm_num, if_true, ByteArray.size_extract]
          omega)))
    · by_cases hlt31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)) = ⟨0⟩
      · -- SHORT (0 < len < 32)
        have hlt32 : (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)).toNat < 32 := by
          have := weth9StringLen_toNat_le31 hlt31; omega
        exact weth9ReEquivExecTransport hcode
          (weth9NameStringShortReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hlen0 hlt31)
          (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
          (by rw [nameTransition]; exact hbody) rfl hAccounts
          (returnEquiv_of_encode (by
            rw [hHbr, if_pos hlt32]; exact weth9EncodeShort _ hlen0 hlt31))
      · -- LONG (len ≥ 32)
        have hge31 : UInt256.lt ⟨31⟩ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)) ≠ ⟨0⟩ := hlt31
        have hge32 : ¬ (weth9StringLen (weth9StringSlotWord σ_evm I ⟨0⟩)).toNat < 32 := by
          have := weth9LongLen_ge32 hge31; omega
        exact weth9ReEquivExecTransport hcode
          (weth9NameStringLongReturns (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel hge31
            (weth9NameReturnSizeBound σ_evm I))
          (weth9SelectorDispatchName hsel) (weth9Decode_name_ok hsz4)
          (by rw [nameTransition]; exact hbody) rfl hAccounts
          (returnEquiv_of_encode (by
            rw [hHbr, if_neg hge32, weth9DataWords_bridge hAccounts ⟨0⟩]
            exact weth9NameEncode_long hge31 (weth9NameReturnSizeBound σ_evm I)))
  · -- non-payable revert: EVM reverts at name's callvalue guard (entry 166, gt 178).
    obtain ⟨_, _, h166⟩ := weth9ReachName (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨178⟩) h166 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchName hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
