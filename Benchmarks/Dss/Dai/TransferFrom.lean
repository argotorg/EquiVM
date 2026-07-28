import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and external wrapper for `transferFrom(address,address,uint256)` -/

abbrev transferFromSrcWord (I : ExecutionEnv) : UInt256 :=
  if selIs I (daiSelBytes 18) then solcSourceWord I
  else if selIs I (daiSelBytes 14) then solcSourceWord I
  else calldataWord I.calldata 4

abbrev transferFromSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromSrcWord I)

abbrev transferFromDstWord (I : ExecutionEnv) : UInt256 :=
  if selIs I (daiSelBytes 18) then calldataWord I.calldata 4
  else if selIs I (daiSelBytes 14) then calldataWord I.calldata 4
  else if selIs I (daiSelBytes 13) then solcSourceWord I
  else if selIs I (daiSelBytes 8) then calldataWord I.calldata 36
  else calldataWord I.calldata 36

abbrev transferFromDstMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromDstWord I)

abbrev transferFromWadWord (I : ExecutionEnv) : UInt256 :=
  if selIs I (daiSelBytes 18) then calldataWord I.calldata 36
  else if selIs I (daiSelBytes 14) then calldataWord I.calldata 36
  else if selIs I (daiSelBytes 13) then calldataWord I.calldata 36
  else calldataWord I.calldata 68

theorem selIs_eq_of_selIs {I : ExecutionEnv} {a b : ByteArray}
    (ha : selIs I a) (hb : selIs I b) : a = b := by
  exact (byteArray_eq_of_beq ha).trans (byteArray_eq_of_beq hb).symm

theorem not_selIs_of_selIs_ne {I : ExecutionEnv} {a b : ByteArray}
    (ha : selIs I a) (hne : a ≠ b) : ¬ selIs I b := by
  intro hb
  exact hne (selIs_eq_of_selIs ha hb)

theorem transferFromSrcWord_of_transfer (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18)) :
    transferFromSrcWord I = solcSourceWord I := by
  simp [transferFromSrcWord, hsel]

theorem transferFromDstWord_of_transfer (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18)) :
    transferFromDstWord I = calldataWord I.calldata 4 := by
  simp [transferFromDstWord, hsel]

theorem transferFromWadWord_of_transfer (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 18)) :
    transferFromWadWord I = calldataWord I.calldata 36 := by
  simp [transferFromWadWord, hsel]

theorem transferFromSrcWord_of_push (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14)) :
    transferFromSrcWord I = solcSourceWord I := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromSrcWord
  rw [if_neg hnot18, if_pos hsel]

theorem transferFromDstWord_of_push (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14)) :
    transferFromDstWord I = calldataWord I.calldata 4 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromDstWord
  rw [if_neg hnot18, if_pos hsel]

theorem transferFromWadWord_of_push (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 14)) :
    transferFromWadWord I = calldataWord I.calldata 36 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromWadWord
  rw [if_neg hnot18, if_pos hsel]

theorem transferFromSrcWord_of_pull (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 13)) :
    transferFromSrcWord I = calldataWord I.calldata 4 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromSrcWord
  rw [if_neg hnot18, if_neg hnot14]

theorem transferFromDstWord_of_pull (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 13)) :
    transferFromDstWord I = solcSourceWord I := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromDstWord
  rw [if_neg hnot18, if_neg hnot14, if_pos hsel]

theorem transferFromWadWord_of_pull (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 13)) :
    transferFromWadWord I = calldataWord I.calldata 36 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromWadWord
  rw [if_neg hnot18, if_neg hnot14, if_pos hsel]

theorem transferFromSrcWord_of_move (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 8)) :
    transferFromSrcWord I = calldataWord I.calldata 4 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromSrcWord
  rw [if_neg hnot18, if_neg hnot14]

theorem transferFromDstWord_of_move (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 8)) :
    transferFromDstWord I = calldataWord I.calldata 36 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot13 : ¬ selIs I (daiSelBytes 13) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromDstWord
  rw [if_neg hnot18, if_neg hnot14, if_neg hnot13, if_pos hsel]

theorem transferFromWadWord_of_move (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 8)) :
    transferFromWadWord I = calldataWord I.calldata 68 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot13 : ¬ selIs I (daiSelBytes 13) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromWadWord
  rw [if_neg hnot18, if_neg hnot14, if_neg hnot13]

theorem transferFromSrcWord_of_transferFrom (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 19)) :
    transferFromSrcWord I = calldataWord I.calldata 4 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromSrcWord
  rw [if_neg hnot18, if_neg hnot14]

theorem transferFromDstWord_of_transferFrom (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 19)) :
    transferFromDstWord I = calldataWord I.calldata 36 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot13 : ¬ selIs I (daiSelBytes 13) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot8 : ¬ selIs I (daiSelBytes 8) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromDstWord
  rw [if_neg hnot18, if_neg hnot14, if_neg hnot13, if_neg hnot8]

theorem transferFromWadWord_of_transferFrom (I : ExecutionEnv)
    (hsel : selIs I (daiSelBytes 19)) :
    transferFromWadWord I = calldataWord I.calldata 68 := by
  have hnot18 : ¬ selIs I (daiSelBytes 18) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot14 : ¬ selIs I (daiSelBytes 14) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  have hnot13 : ¬ selIs I (daiSelBytes 13) :=
    not_selIs_of_selIs_ne hsel (by native_decide)
  unfold transferFromWadWord
  rw [if_neg hnot18, if_neg hnot14, if_neg hnot13]

abbrev transferFromSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromSrcWord I).toNat)

abbrev transferFromDstValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromDstWord I).toNat)

abbrev transferFromWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromWadWord I).toNat)

abbrev transferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "src" (transferFromSrcValue I)).insert "dst"
    (transferFromDstValue I)).insert "wad" (transferFromWadValue I)

abbrev transferFromCallStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "wad" (transferFromWadValue I)).insert "dst"
    (transferFromDstValue I)).insert "src" (transferFromSrcValue I)

theorem transferFromStore_get_src (I : ExecutionEnv) :
    (transferFromStore I).get? "src" = some (transferFromSrcValue I) := by
  unfold transferFromStore
  rw [store_get_ne
    (L := ((∅ : Store).insert "src" (transferFromSrcValue I)).insert "dst"
      (transferFromDstValue I))
    (k := "wad") (a := "src") (transferFromWadValue I) (by native_decide)]
  rw [store_get_ne
    (L := (∅ : Store).insert "src" (transferFromSrcValue I))
    (k := "dst") (a := "src") (transferFromDstValue I) (by native_decide)]
  simp

theorem transferFromStore_get_dst (I : ExecutionEnv) :
    (transferFromStore I).get? "dst" = some (transferFromDstValue I) := by
  unfold transferFromStore
  rw [store_get_ne
    (L := ((∅ : Store).insert "src" (transferFromSrcValue I)).insert "dst"
      (transferFromDstValue I))
    (k := "wad") (a := "dst") (transferFromWadValue I) (by native_decide)]
  simp

theorem transferFromStore_get_wad (I : ExecutionEnv) :
    (transferFromStore I).get? "wad" = some (transferFromWadValue I) := by
  unfold transferFromStore
  simp

theorem transferFromCallStore_get_src (I : ExecutionEnv) :
    (transferFromCallStore I).get? "src" = some (transferFromSrcValue I) := by
  unfold transferFromCallStore
  simp

theorem transferFromCallStore_get_dst (I : ExecutionEnv) :
    (transferFromCallStore I).get? "dst" = some (transferFromDstValue I) := by
  unfold transferFromCallStore
  rw [store_get_ne
    (L := ((∅ : Store).insert "wad" (transferFromWadValue I)).insert "dst"
      (transferFromDstValue I))
    (k := "src") (a := "dst") (transferFromSrcValue I) (by native_decide)]
  simp

theorem transferFromCallStore_get_wad (I : ExecutionEnv) :
    (transferFromCallStore I).get? "wad" = some (transferFromWadValue I) := by
  unfold transferFromCallStore
  rw [store_get_ne
    (L := ((∅ : Store).insert "wad" (transferFromWadValue I)).insert "dst"
      (transferFromDstValue I))
    (k := "src") (a := "wad") (transferFromSrcValue I) (by native_decide)]
  rw [store_get_ne
    (L := (∅ : Store).insert "wad" (transferFromWadValue I))
    (k := "dst") (a := "wad") (transferFromDstValue I) (by native_decide)]
  simp

theorem daiBindTransferFromCallStore (I : ExecutionEnv) :
    bindParams? transferFromTransition.params
        [transferFromSrcValue I, transferFromDstValue I, transferFromWadValue I] =
      some (transferFromCallStore I) := by
  rfl

theorem daiDecode_transferFrom_ok {I : ExecutionEnv}
    (hsel : selIs I (daiSelBytes 19)) (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"] [addr, addr, uint256]
    I.calldata = _
  unfold transferFromStore transferFromSrcValue transferFromDstValue transferFromWadValue
  rw [transferFromSrcWord_of_transferFrom I hsel,
    transferFromDstWord_of_transferFrom I hsel,
    transferFromWadWord_of_transferFrom I hsel]
  change decodeCalldataWithMode DecodeMode.legacySolc05 ["src", "dst", "wad"]
      [abiAddress, abiAddress, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "src"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "dst"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert "wad"
      (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_legacyAddress_legacyAddress_uint256_ok
    (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz100

theorem daiDecode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"] [addr, addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "src") (y := "dst") (z := "wad") hsz4 hshort

theorem daiTransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsel : selIs I (daiSelBytes 19))
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨542⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1411⟩
        [transferFromWadWord I, transferFromDstMaskedWord I,
          transferFromSrcMaskedWord I, ⟨496⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd564⟩ := RD.daiAddressAddressUint256ExternalLenOk
    (entry := ⟨542⟩) (ret := ⟨496⟩) (routine := ⟨1411⟩) hreach
    dai_address_address_uint256_external_entry_wf (by jump_dest) hsz100 hsize
  obtain ⟨_, _, rd1411⟩ := RD.daiAddressAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨542⟩) (ret := ⟨496⟩) (routine := ⟨1411⟩) (R := [sel])
    rd564 dai_address_address_uint256_external_entry_wf (by jump_dest)
    (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    rw [transferFromWadWord_of_transferFrom I hsel,
      transferFromDstMaskedWord, transferFromDstWord_of_transferFrom I hsel,
      transferFromSrcMaskedWord, transferFromSrcWord_of_transferFrom I hsel]
    simpa [calldataWord] using rd1411⟩

theorem daiTransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD daiBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨542⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.daiAddressAddressUint256ExternalShort
    (entry := ⟨542⟩) (ret := ⟨496⟩) (routine := ⟨1411⟩)
    hreach dai_address_address_uint256_external_entry_wf hsz4 hsize hshort

/-! ## Source-level storage state for `transferFrom` -/

abbrev transferFromSrcKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (transferFromSrcWord I).toNat)

abbrev transferFromDstKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (transferFromDstWord I).toNat)

abbrev transferFromSpenderKey (evm : EVM.State) : KeyValue :=
  .address evm.executionEnv.source

def transferFromSrcSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (transferFromSrcKey I)

def transferFromDstSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (transferFromDstKey I)

def transferFromAllowanceSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (transferFromSrcKey I) (transferFromSpenderKey evm)

theorem transferFromSrcSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    transferFromSrcSlot I = mapSlot (transferFromSrcMaskedWord I) ⟨2⟩ := by
  unfold transferFromSrcSlot balanceOfSlot transferFromSrcKey transferFromSrcMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem transferFromDstSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    transferFromDstSlot I = mapSlot (transferFromDstMaskedWord I) ⟨2⟩ := by
  unfold transferFromDstSlot balanceOfSlot transferFromDstKey transferFromDstMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

theorem transferFromSrcMaskedWord_eq_solcSourceWord_of_address_eq (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = I.source) :
    transferFromSrcMaskedWord I = solcSourceWord I := by
  have hmask := keyValueToWord_address_ofNat_mask (transferFromSrcWord I)
  rw [heq, keyValueToWord_address] at hmask
  exact hmask.symm

theorem transferFrom_address_eq_of_srcMaskedWord_eq (I : ExecutionEnv)
    (heq : transferFromSrcMaskedWord I = solcSourceWord I) :
    AccountAddress.ofNat (transferFromSrcWord I).toNat = I.source := by
  have hmaskAddr :
      AccountAddress.ofNat (transferFromSrcWord I).toNat =
        AccountAddress.ofNat (UInt256.land (transferFromSrcWord I) solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change (transferFromSrcWord I).val.val % AccountAddress.size =
      Nat.land (transferFromSrcWord I).val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hmasked : AccountAddress.ofNat
      (UInt256.land (transferFromSrcWord I) solcAddrMask).toNat = I.source := by
    apply solcMaskedAddress_eq_source_of_word_eq
    rw [u256_land_comm]
    simpa [transferFromSrcMaskedWord] using heq
  exact hmaskAddr.trans hmasked

theorem transferFromAllowanceSlot_eq_mapSlot_masked (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    transferFromAllowanceSlot evm I =
      mapSlot (solcSourceWord I) (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩) := by
  unfold transferFromAllowanceSlot allowanceSlot allowanceOwnerSlot transferFromSrcKey
    transferFromSpenderKey transferFromSrcMaskedWord solcSourceWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address, hsrc]

theorem transferFromSrcMaskedWord_canonical (I : ExecutionEnv) :
    (transferFromSrcMaskedWord I).toNat < EVM.addressModulus := by
  unfold transferFromSrcMaskedWord
  rw [u256_land_comm solcAddrMask (transferFromSrcWord I)]
  exact solcAddrMask_result_canonical (transferFromSrcWord I)

theorem transferFromDstMaskedWord_canonical (I : ExecutionEnv) :
    (transferFromDstMaskedWord I).toNat < EVM.addressModulus := by
  unfold transferFromDstMaskedWord
  rw [u256_land_comm solcAddrMask (transferFromDstWord I)]
  exact solcAddrMask_result_canonical (transferFromDstWord I)

noncomputable abbrev transferFromSrcHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ solcFreePtrMem

noncomputable abbrev transferFromAllowanceHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromSrcHashMem I)

noncomputable abbrev transferFromDstHashMem (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem (transferFromDstMaskedWord I)
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩
      (transferFromSrcHashMem I))

theorem transferFromSrcHashMem_size (I : ExecutionEnv) :
    (transferFromSrcHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ solcFreePtrMem_size

theorem transferFromSrcHashMem_read64 (I : ExecutionEnv) :
    (transferFromSrcHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (transferFromSrcMaskedWord I) ⟨2⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem transferFromAllowanceHashMem_size (I : ExecutionEnv) :
    (transferFromAllowanceHashMem I).size = 96 := by
  unfold transferFromAllowanceHashMem solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 (solcSourceWord I)
    (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
    (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
      (transferFromSrcHashMem_size I))

theorem transferFromAllowanceHashMem_read64 (I : ExecutionEnv) :
    (transferFromAllowanceHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromAllowanceHashMem solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 (solcSourceWord I)
    (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
    (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
      (transferFromSrcHashMem_size I))
    (twoWordHashMem_read64 (transferFromSrcMaskedWord I) ⟨3⟩
      (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I))

theorem solcNestedMappingCallerHashMem_size_96 {mem : ByteArray}
    (baseSlot owner : UInt256) (I : ExecutionEnv) (hmem : mem.size = 96) :
    (solcNestedMappingCallerHashMem baseSlot owner I mem).size = 96 := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 (solcSourceWord I) (solcMappingSlot baseSlot owner)
    (twoWordHashMem_size_96 owner baseSlot hmem)

theorem solcNestedMappingCallerHashMem_read64_96 {mem : ByteArray}
    (baseSlot owner : UInt256) (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcNestedMappingCallerHashMem baseSlot owner I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 (solcSourceWord I) (solcMappingSlot baseSlot owner)
    (twoWordHashMem_size_96 owner baseSlot hmem)
    (twoWordHashMem_read64 owner baseSlot hmem hread64)

noncomputable abbrev transferFromAllowanceReloadHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceHashMem I)

noncomputable abbrev transferFromAllowanceStoreHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceReloadHashMem I)

theorem transferFromAllowanceReloadHashMem_size (I : ExecutionEnv) :
    (transferFromAllowanceReloadHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceHashMem_size I)

theorem transferFromAllowanceReloadHashMem_read64 (I : ExecutionEnv) :
    (transferFromAllowanceReloadHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceHashMem_size I) (transferFromAllowanceHashMem_read64 I)

theorem transferFromAllowanceStoreHashMem_size (I : ExecutionEnv) :
    (transferFromAllowanceStoreHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceReloadHashMem_size I)

theorem transferFromAllowanceStoreHashMem_read64 (I : ExecutionEnv) :
    (transferFromAllowanceStoreHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceReloadHashMem_size I) (transferFromAllowanceReloadHashMem_read64 I)

theorem transferFromDstHashMem_size (I : ExecutionEnv) :
    (transferFromDstHashMem I).size = 96 := by
  unfold transferFromDstHashMem
  exact wordAt0Mem_size_96 (transferFromDstMaskedWord I)
    (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩
      (transferFromSrcHashMem_size I))

theorem transferFromDstHashMem_read64 (I : ExecutionEnv) :
    (transferFromDstHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold transferFromDstHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by
      rw [twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩
        (transferFromSrcHashMem_size I)]
      omega)
    (by omega)
    (by
      rw [twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩
        (transferFromSrcHashMem_size I)])]
  exact twoWordHashMem_read64 (transferFromSrcMaskedWord I) ⟨2⟩
    (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I)

noncomputable abbrev transferFromLogMem (value : UInt256) (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (transferFromDstHashMem I) value

noncomputable abbrev transferFromBoolReturnMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
    (transferFromLogMem (transferFromWadWord I) I) 128 32

theorem transferFromLogMem_mload64 (value : UInt256) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferFromLogMem value I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferFromLogMem value I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 value (transferFromDstHashMem_size I)
    (transferFromDstHashMem_read64 I)

theorem transferFromBoolReturnMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferFromBoolReturnMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((transferFromBoolReturnMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue (by
      unfold transferFromBoolReturnMem transferFromLogMem
      rw [toByteArray_write32_size_of_le
        (solcScratchReturnMem (transferFromDstHashMem I) (transferFromWadWord I))
        (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
        (solcScratchReturnMem_size (transferFromWadWord I) (transferFromDstHashMem_size I))
        (by
          rw [solcScratchReturnMem_size (transferFromWadWord I)
            (transferFromDstHashMem_size I)]
          decide)
        (by decide)]
      decide)
    (by decide)
    (by
      unfold transferFromBoolReturnMem transferFromLogMem
      rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
        (by
          rw [solcScratchReturnMem_size (transferFromWadWord I)
            (transferFromDstHashMem_size I)]
          omega)
        (by omega)]
      exact solcScratchReturnMem_read64 (transferFromWadWord I)
        (transferFromDstHashMem_size I) (transferFromDstHashMem_read64 I))

theorem transferFromBoolReturnMem_read128 (I : ExecutionEnv) :
    (transferFromBoolReturnMem I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
  unfold transferFromBoolReturnMem transferFromLogMem
  exact toByteArray_write32_read_back (solcScratchReturnMem (transferFromDstHashMem I)
    (transferFromWadWord I)) (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
    (by
      rw [solcScratchReturnMem_size (transferFromWadWord I) (transferFromDstHashMem_size I)]
      decide)

theorem wordAt0Mem_read64_of_size_96 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96) :
    (wordAt0Mem word mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega) (by rw [hmem])]

theorem wordAt0Mem_solcMappingSlot_of_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread32 : mem.readWithPadding 32 32 = UInt256.toByteArray slot) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem key mem).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  have hread0 :
      (wordAt0Mem key mem).readWithPadding 0 32 = UInt256.toByteArray key :=
    wordAt0Mem_read0 key mem
  have hread32' :
      (wordAt0Mem key mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [hmem]; omega)
      (by omega)
      (by rw [hmem]; omega)]
    exact hread32
  have hread0_64 :
      (wordAt0Mem key mem).readWithPadding 0 64 =
        UInt256.toByteArray key ++ UInt256.toByteArray slot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [wordAt0Mem_size_96 key hmem]; omega)]
    have hleft :
        (wordAt0Mem key mem).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0
          (by rw [wordAt0Mem_size_96 key hmem]; omega),
        hread0]
    have hright :
        (wordAt0Mem key mem).extract 32 64 = UInt256.toByteArray slot := by
      rw [← readWithPadding_eq_extract _ 32
          (by rw [wordAt0Mem_size_96 key hmem]; omega),
        hread32']
    rw [show (wordAt0Mem key mem).extract 0 64 =
        (wordAt0Mem key mem).extract 0 32 ++
          (wordAt0Mem key mem).extract 32 64 by
        rw [ByteArray.extract_append_extract]
        norm_num]
    rw [hleft, hright]
  rw [hread0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

noncomputable abbrev transferFromTailSrcStoreMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem)

noncomputable abbrev transferFromTailDstStoreMem (mem : ByteArray) (I : ExecutionEnv) :
    ByteArray :=
  twoWordHashMem (transferFromDstMaskedWord I) ⟨2⟩
    (wordAt0Mem (transferFromDstMaskedWord I) (transferFromTailSrcStoreMem mem I))

noncomputable abbrev transferFromTailBoolReturnMem
    (scratch : ByteArray) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
    (solcScratchReturnMem scratch (transferFromWadWord I)) 128 32

theorem transferFromTailSrcStoreMem_size {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96) :
    (transferFromTailSrcStoreMem mem I).size = 96 := by
  exact twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩
    (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)

theorem transferFromTailSrcStoreMem_read64 {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromTailSrcStoreMem mem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (transferFromSrcMaskedWord I) ⟨2⟩
    (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)
    (twoWordHashMem_read64 (transferFromSrcMaskedWord I) ⟨2⟩ hmem hread64)

theorem transferFromTailDstStoreMem_size {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96) :
    (transferFromTailDstStoreMem mem I).size = 96 := by
  exact twoWordHashMem_size_96 (transferFromDstMaskedWord I) ⟨2⟩
    (wordAt0Mem_size_96 (transferFromDstMaskedWord I)
      (transferFromTailSrcStoreMem_size I hmem))

theorem transferFromTailDstStoreMem_read64 {mem : ByteArray} (I : ExecutionEnv)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (transferFromTailDstStoreMem mem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (transferFromDstMaskedWord I) ⟨2⟩
    (wordAt0Mem_size_96 (transferFromDstMaskedWord I)
      (transferFromTailSrcStoreMem_size I hmem))
    (by
      rw [wordAt0Mem_read64_of_size_96 (transferFromDstMaskedWord I)
        (transferFromTailSrcStoreMem_size I hmem)]
      exact transferFromTailSrcStoreMem_read64 I hmem hread64)

theorem transferFromTailBoolReturnMem_mload64 {scratch : ByteArray} (I : ExecutionEnv)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferFromTailBoolReturnMem scratch I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((transferFromTailBoolReturnMem scratch I).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue (by
      unfold transferFromTailBoolReturnMem
      rw [toByteArray_write32_size_of_le
        (solcScratchReturnMem scratch (transferFromWadWord I))
        (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
        (solcScratchReturnMem_size (transferFromWadWord I) hscratch)
        (by
          rw [solcScratchReturnMem_size (transferFromWadWord I) hscratch]
          decide)
        (by decide)]
      decide)
    (by decide)
    (by
      unfold transferFromTailBoolReturnMem
      rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
        (by
          rw [solcScratchReturnMem_size (transferFromWadWord I) hscratch]
          omega)
        (by omega)]
      exact solcScratchReturnMem_read64 (transferFromWadWord I) hscratch hread64)

theorem transferFromTailBoolReturnMem_read128 {scratch : ByteArray} (I : ExecutionEnv)
    (hscratch : scratch.size = 96) :
    (transferFromTailBoolReturnMem scratch I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
  unfold transferFromTailBoolReturnMem
  exact toByteArray_write32_read_back
    (solcScratchReturnMem scratch (transferFromWadWord I))
    (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
    (by
      rw [solcScratchReturnMem_size (transferFromWadWord I) hscratch]
      decide)

abbrev transferFromTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

abbrev transferFromEvmSrcSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (transferFromSrcMaskedWord I) ⟨2⟩

abbrev transferFromEvmDstSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (transferFromDstMaskedWord I) ⟨2⟩

abbrev transferFromEvmAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (solcSourceWord I) (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)

abbrev transferFromEvmTailSrcBalanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (transferFromEvmSrcSlot I)

abbrev transferFromEvmAllowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (transferFromEvmAllowanceSlot I)

abbrev transferFromEvmAllowanceDebitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (transferFromEvmAllowanceWord σ I) (transferFromWadWord I)

abbrev transferFromEvmAfterAllowanceAccountMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (transferFromEvmAllowanceSlot I)
    (transferFromEvmAllowanceDebitWord σ I)

abbrev transferFromEvmTailSrcDebitWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (transferFromEvmTailSrcBalanceWord σ I) (transferFromWadWord I)

abbrev transferFromEvmTailAfterSrcAccountMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (transferFromEvmSrcSlot I)
    (transferFromEvmTailSrcDebitWord σ I)

abbrev transferFromEvmTailDstBalanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord (transferFromEvmTailAfterSrcAccountMap σ I) I (transferFromEvmDstSlot I)

abbrev transferFromEvmTailDstCreditWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  transferFromEvmTailDstBalanceWord σ I + transferFromWadWord I

abbrev transferFromEvmTailPostAccountMap (σ : AccountMap) (I : ExecutionEnv) :
    AccountMap :=
  sstoreAccountMap I.codeOwner (transferFromEvmTailAfterSrcAccountMap σ I)
    (transferFromEvmDstSlot I) (transferFromEvmTailDstCreditWord σ I)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_logAndJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256} {scratch rdata : ByteArray}
    (hperm : I.perm = true)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨1901⟩
      (⟨64⟩ :: transferFromDstMaskedWord I :: solcAddrMask :: ⟨32⟩ :: ⟨0⟩ ::
        transferFromWadWord I :: transferFromDstMaskedWord I :: transferFromSrcMaskedWord I ::
        ret :: S)
      scratch (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem scratch (transferFromWadWord I)) (UInt256.ofNat 5) rdata
      (cA, σ) k' C' := by
  have hsrcMask : UInt256.land (transferFromSrcMaskedWord I) solcAddrMask =
      transferFromSrcMaskedWord I :=
    solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ scratch.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (scratch.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hscratch]; decide) (by decide) hread64
  have rd2 := evm_run h with [
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4 := evm_run rd2 with [
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5 := rd4.mstore 6 (solcScratchReturnMem scratch (transferFromWadWord I))
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd12 := evm_run rd5 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (solcScratchReturnMem_mload64 (transferFromWadWord I) hscratch hread64)
      (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMask] at rd12
  have rd13 := evm_run rd12 with [raw swap3 (by native_decide) (by evm_ov)]
  have rd46 := rd13.pushConst transferFromTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd53 := evm_run rd46 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd54 := rd53.log3 0 (UInt256.ofNat 5) (by native_decide) hperm mem_cost
    (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRet := evm_run rd54 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) hretDest (by evm_ov)]
  exact ⟨_, _, rdRet⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_logAndReturn {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {scratch rdata : ByteArray}
    (hperm : I.perm = true)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD daiBytecode I g s0 ⟨1901⟩
      [⟨64⟩, transferFromDstMaskedWord I, solcAddrMask, ⟨32⟩, ⟨0⟩,
        transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨496⟩, sel]
      scratch (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, σ) (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd496⟩ := daiTransferFromX_logAndJump
    (I := I) (ret := ⟨496⟩) (S := [sel]) (scratch := scratch)
    hperm hscratch hread64 (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) (by simpa using h)
  have hretWf : solcReturnBoolFromMemWf daiBytecode ⟨496⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool :
      UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by
    native_decide
  simpa [hbool, transferFromTailBoolReturnMem] using
    RD.solcReturnBoolFromMem rd496 hretWf
      (solcScratchReturnMem_mload64 (transferFromWadWord I) hscratch hread64)
      (by rfl)
      (transferFromTailBoolReturnMem_mload64 I hscratch hread64)
      (transferFromTailBoolReturnMem_read128 I hscratch)
      (by simp only [List.length_cons, List.length_nil]; omega)

def transferFromSrcBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromSrcSlot I)

def transferFromDstBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromDstSlot I)

def transferFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

theorem transferFromSrcBalanceWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromSrcBalanceWord (initState cA gh bl σ σ₀ g A I) I =
      transferFromEvmTailSrcBalanceWord σ I := by
  simp [transferFromSrcBalanceWord, transferFromEvmTailSrcBalanceWord,
    transferFromEvmSrcSlot, transferFromSrcSlot_eq_mapSlot_masked, initState,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord]

theorem transferFromDstBalanceWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromDstBalanceWord (initState cA gh bl σ σ₀ g A I) I =
      solcSlotWord σ I (transferFromEvmDstSlot I) := by
  simp [transferFromDstBalanceWord, transferFromEvmDstSlot,
    transferFromDstSlot_eq_mapSlot_masked, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord]

theorem transferFromAllowanceWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferFromAllowanceWord (initState cA gh bl σ σ₀ g A I) I =
      transferFromEvmAllowanceWord σ I := by
  unfold transferFromAllowanceWord
  rw [show transferFromAllowanceSlot (initState cA gh bl σ σ₀ g A I) I =
      transferFromEvmAllowanceSlot I by
    simpa [initState, transferFromEvmAllowanceSlot] using
      transferFromAllowanceSlot_eq_mapSlot_masked
        (initState cA gh bl σ σ₀ g A I) I (by simp [initState])]
  simp [transferFromEvmAllowanceWord, initState, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord]

abbrev transferFromSrcBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromSrcBalanceWord evm I).toNat)

abbrev transferFromDstBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromDstBalanceWord evm I).toNat)

abbrev transferFromAllowanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromAllowanceWord evm I).toNat)

def transferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat)

def transferFromSrcDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat)

def transferFromDstCreditNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferFromDstBalanceWord evm I).toNat + (transferFromWadWord I).toNat

def transferFromDstCreditWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferFromDstCreditNat evm I)

theorem transferFromDstCreditWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat evm I < UInt256.size) :
    (transferFromDstCreditWord evm I).toNat = transferFromDstCreditNat evm I := by
  unfold transferFromDstCreditWord
  exact ulit_toNat' _ hfit

abbrev transferFromDstCreditValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromDstCreditNat evm I))

def transferFromAfterAllowanceState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)
    (transferFromAllowanceDebitWord evm I)

theorem transferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterAllowanceState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [transferFromAfterAllowanceState, storageStore_executionEnv]

def transferFromAfterSrcDebitState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferFromSrcSlot I)
    (transferFromSrcDebitWord evm I)

theorem transferFromAfterSrcDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferFromAfterSrcDebitState evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [transferFromAfterSrcDebitState, storageStore_executionEnv]

def transferFromPostStateFrom (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferFromAfterSrcDebitState evm I) evm.executionEnv.codeOwner
    (transferFromDstSlot I) (transferFromDstCreditWord (transferFromAfterSrcDebitState evm I) I)

abbrev transferFromSrcBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (transferFromSrcKey I)] }

abbrev transferFromDstBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (transferFromDstKey I)] }

abbrev transferFromAllowanceRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (transferFromSrcKey I), .mindex (transferFromSpenderKey evm)] }

theorem transferFromStore_allowance (I : ExecutionEnv) :
    (transferFromStore I).get? "allowance" = none := by
  unfold transferFromStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem transferFromStore_balanceOf (I : ExecutionEnv) :
    (transferFromStore I).get? "balanceOf" = none := by
  unfold transferFromStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem transferFromStore_index_src (I : ExecutionEnv) :
    (transferFromStore I)["src"] = transferFromSrcValue I := by
  unfold transferFromStore
  simp [Std.HashMap.getElem_insert]

theorem transferFromStore_index_dst (I : ExecutionEnv) :
    (transferFromStore I)["dst"] = transferFromDstValue I := by
  unfold transferFromStore
  simp [Std.HashMap.getElem_insert]

theorem evalExpr_transferFrom_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "wad") = .ok (transferFromWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_get_wad]

theorem evalExpr_transferFrom_src (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "src") = .ok (transferFromSrcValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_get_src]

theorem evalExpr_transferFrom_dst (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.var "dst") = .ok (transferFromDstValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromStore_get_dst]

theorem evalStorageRef_transferFrom_src_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (balanceOfRef (.var "src")) = .ok (transferFromSrcBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromSrcBalanceRef,
    transferFromSrcValue, transferFromSrcKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?, transferFromStore_index_src]

theorem evalStorageRef_transferFrom_dst_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (balanceOfRef (.var "dst")) = .ok (transferFromDstBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromDstBalanceRef,
    transferFromDstValue, transferFromDstKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?, transferFromStore_index_dst]

theorem evalStorageRef_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromStore I } evm
      (allowanceRef (.var "src") sender) = .ok (transferFromAllowanceRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    transferFromAllowanceRef, transferFromSrcValue, transferFromSrcKey,
    transferFromSpenderKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?, transferFromStore_index_src]

theorem evalExpr_transferFrom_src_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (balanceOfRef (.var "src"))) =
        .ok (transferFromSrcBalanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromStore I })
    (slot := balanceOfRef (.var "src"))
    (er := transferFromSrcBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromSrcSlot I) (.int uint256Int))
    (value := transferFromSrcBalanceValue evm I)
    (hbase := by
      simpa [balanceOfRef] using transferFromStore_balanceOf I)
    (her := evalStorageRef_transferFrom_src_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
        uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromSrcBalanceWord] using
        storageLocLoad_uint256 evm (transferFromSrcSlot I))]

theorem evalExpr_transferFrom_dst_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (balanceOfRef (.var "dst"))) =
        .ok (transferFromDstBalanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromStore I })
    (slot := balanceOfRef (.var "dst"))
    (er := transferFromDstBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromDstSlot I) (.int uint256Int))
    (value := transferFromDstBalanceValue evm I)
    (hbase := by
      simpa [balanceOfRef] using transferFromStore_balanceOf I)
    (her := evalStorageRef_transferFrom_dst_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromDstKey,
        uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromDstBalanceWord] using
        storageLocLoad_uint256 evm (transferFromDstSlot I))]

theorem evalExpr_transferFrom_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.storage (allowanceRef (.var "src") sender)) =
        .ok (transferFromAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromStore I })
    (slot := allowanceRef (.var "src") sender)
    (er := transferFromAllowanceRef evm I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromAllowanceSlot evm I) (.int uint256Int))
    (value := transferFromAllowanceValue evm I)
    (hbase := by
      simpa [allowanceRef] using transferFromStore_allowance I)
    (her := evalStorageRef_transferFrom_allowance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
        transferFromSpenderKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromAllowanceWord] using
        storageLocLoad_uint256 evm (transferFromAllowanceSlot evm I))]

theorem evalExpr_transferFrom_src_balance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_balance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue,
    transferFromWadValue, henough]

theorem evalExpr_transferFrom_src_balance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromSrcBalanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_balance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue,
    transferFromWadValue]
  omega

theorem evalExpr_transferFrom_allowance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, henough]

theorem evalExpr_transferFrom_allowance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromAllowanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem evalExpr_transferFrom_src_ne_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue,
    transferFromSrcValue, hne]

theorem evalExpr_transferFrom_src_ne_sender_false (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue,
    transferFromSrcValue, heq]

theorem evalExpr_transferFrom_allowance_ne_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance]
  rw [show evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue, maxUint256]
  intro h
  apply hnotMax
  apply Int.ofNat.inj
  have hmaxInt : Int.ofNat (UInt256.size - 1) =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Int) := by
    norm_num [UInt256.size]
  rw [hmaxInt]
  exact h

theorem evalExpr_transferFrom_allowance_ne_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance]
  rw [show evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue, maxUint256,
    UInt256.size, hmax]

theorem evalExpr_transferFrom_allowanceNeedsSpend_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool true) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_transferFrom_allowance_ne_max_true evm I hnotMax]

theorem evalExpr_transferFrom_allowanceNeedsSpend_false_sender
    (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_ne_sender_false evm I heq]
  simp only [EvalResult.bind, bind, evalExpr?, pure]

theorem evalExpr_transferFrom_allowanceNeedsSpend_false_max (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_transferFrom_allowance_ne_max_false evm I hmax]

theorem evalExpr_transferFrom_allowance_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromAllowanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (sub256 (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromAllowanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat =
        Int.ofNat ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromAllowanceWord evm I).val.isLt)
  have hltNat :
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (transferFromAllowanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) ≥
      (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg : ¬
      (Int.ofNat ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound : ¬
      115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFrom_allowance_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFrom_src_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromSrcBalanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_balance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_src_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (sub256 (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromSrcDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSrcBalanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat =
        Int.ofNat ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromSrcDebitWord evm I).toNat =
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromSrcDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromSrcBalanceWord evm I).val.isLt)
  have hltNat :
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (transferFromSrcBalanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) ≥
      (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg : ¬
      (Int.ofNat ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound : ¬
      115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFrom_src_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFrom_dst_add_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromDstBalanceWord evm I).toNat +
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_dst_balance, evalExpr_transferFrom_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_dst_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
        .ok (transferFromDstCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromDstCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFrom_dst_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromWadValue, transferFromDstCreditValue, transferFromDstCreditNat, uint256Int,
    hlt]
  constructor
  · omega
  · have hfitNat :
        (transferFromDstBalanceWord evm I).toNat + (transferFromWadWord I).toNat < 2 ^ 256 := by
      simpa [transferFromDstCreditNat, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_allowance_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .le (sub256 (.storage (allowanceRef (.var "src") sender)) (.var "wad"))
        (.storage (allowanceRef (.var "src") sender))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_allowance_debit evm I henough, evalExpr_transferFrom_allowance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue]
  have hdebit : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (transferFromAllowanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_src_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .le (sub256 (.storage (balanceOfRef (.var "src"))) (.var "wad"))
        (.storage (balanceOfRef (.var "src")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_src_debit evm I henough, evalExpr_transferFrom_src_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue]
  have hdebit : (transferFromSrcDebitWord evm I).toNat =
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromSrcDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (transferFromSrcBalanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_dst_checkedAdd_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad"))
        (.storage (balanceOfRef (.var "dst")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_dst_credit evm I hfit, evalExpr_transferFrom_dst_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromDstCreditValue, transferFromDstCreditNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFrom_dst_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromDstCreditNat evm I) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad")) = .revert := by
  have hge : (2 : Int) ^ 256 ≤ Int.ofNat (transferFromDstCreditNat evm I) := by
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
  have hnotNeg : ¬ Int.ofNat (transferFromDstCreditNat evm I) < 0 := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFrom_dst_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromWadValue, transferFromDstCreditNat, uint256Int, hnotNeg, hge]
  intro _
  simpa [transferFromDstCreditNat] using hge

theorem evalExpr_transferFrom_dst_checkedAdd_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromDstCreditNat evm I) :
    evalExpr? config { contract := contract, locals := transferFromStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad"))
        (.storage (balanceOfRef (.var "dst")))) = .revert := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFrom_dst_credit_revert evm I hover]
  simp [EvalResult.bind, bind]

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I } evm
      .storage (allowanceRef (.var "src") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromAfterAllowanceState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := allowanceRef (.var "src") sender)
      (er := transferFromAllowanceRef evm I)
      (ty := uint256St)
      (loc := wordLoc (transferFromAllowanceSlot evm I) (.int uint256Int))
      (hbase := by
        simpa [allowanceRef] using transferFromStore_allowance I)
      (her := evalStorageRef_transferFrom_allowance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          transferFromSpenderKey, uint256St])
      (hloc := by rfl)
  rw [show wordLoc (transferFromAllowanceSlot evm I) (ElemType.int uint256Int) =
    uint256Loc (transferFromAllowanceSlot evm I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem transferFromAssignSrc (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I } evm
      .storage (balanceOfRef (.var "src"))
      (.int (Int.ofNat (transferFromSrcDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromAfterSrcDebitState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "src"))
      (er := transferFromSrcBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (transferFromSrcSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using transferFromStore_balanceOf I)
      (her := evalStorageRef_transferFrom_src_balance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          uint256St])
      (hloc := by rfl)
  rw [show wordLoc (transferFromSrcSlot I) (ElemType.int uint256Int) =
    uint256Loc (transferFromSrcSlot I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem transferFromAssignDst (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I }
      (transferFromAfterSrcDebitState evm I) .storage (balanceOfRef (.var "dst"))
      (transferFromDstCreditValue (transferFromAfterSrcDebitState evm I) I) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromPostStateFrom evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "dst"))
      (er := transferFromDstBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (transferFromDstSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using transferFromStore_balanceOf I)
      (her := evalStorageRef_transferFrom_dst_balance (transferFromAfterSrcDebitState evm I) I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromDstKey,
          uint256St])
      (hloc := by rfl)
  rw [← transferFromDstCreditWord_toNat (transferFromAfterSrcDebitState evm I) I hfit]
  rw [show wordLoc (transferFromDstSlot I) (ElemType.int uint256Int) =
    uint256Loc (transferFromDstSlot I) by rfl]
  rw [storageLocStore_uint256]
  simp only [transferFromPostStateFrom, transferFromAfterSrcDebit_codeOwner]

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReturns_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hsrcDebitEnough : (transferFromWadWord I).toNat ≤
      (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromDstCreditNat
      (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStore I }
        (transferFromPostStateFrom (transferFromAfterAllowanceState evm I) I)
        (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFrom_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowEnough)
        (transferFromAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFrom_src_balance_ge_true (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFrom_src_checkedSub_true (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_transferFrom_src_debit (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)
        (transferFromAssignSrc (transferFromAfterAllowanceState evm I) I)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFrom_dst_checkedAdd_true
          (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_transferFrom_dst_credit
          (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hfit)
        (transferFromAssignDst (transferFromAfterAllowanceState evm I) I hfit)) ?_
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReturns_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStore I }
        (transferFromPostStateFrom evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromStore I } evm)
      (evalExpr_transferFrom_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_src_debit evm I hsrcEnough)
      (transferFromAssignSrc evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_dst_checkedAdd_true (transferFromAfterSrcDebitState evm I) I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_dst_credit (transferFromAfterSrcDebitState evm I) I hfit)
      (transferFromAssignDst evm I hfit)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReturns_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromStore I }
        (transferFromPostStateFrom evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromStore I } evm)
      (evalExpr_transferFrom_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_src_debit evm I hsrcEnough)
      (transferFromAssignSrc evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_dst_checkedAdd_true (transferFromAfterSrcDebitState evm I) I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_dst_credit (transferFromAfterSrcDebitState evm I) I hfit)
      (transferFromAssignDst evm I hfit)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_initialBalance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromSrcBalanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFrom_src_balance_ge_false evm I hlt))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromAllowanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (result := .reverted)
      (evalExpr_transferFrom_allowanceNeedsSpend_true evm I hne hnotMax)
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_transferFrom_allowance_ge_false evm I hlt))))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_srcDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hltDebit : (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFrom_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowEnough)
        (transferFromAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFrom_src_balance_ge_false (transferFromAfterAllowanceState evm I) I
        hltDebit))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_dstOverflow_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hsrcDebitEnough : (transferFromWadWord I).toNat ≤
      (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromDstCreditNat
      (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFrom_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFrom_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFrom_allowance_debit evm I hallowEnough)
        (transferFromAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_src_balance_ge_true (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFrom_src_checkedSub_true (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFrom_src_debit (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)
      (transferFromAssignSrc (transferFromAfterAllowanceState evm I) I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFrom_dst_checkedAdd_revert
        (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hover))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_dstOverflow_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source)
    (hover : UInt256.size ≤ transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromStore I } evm)
      (evalExpr_transferFrom_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_src_debit evm I hsrcEnough)
      (transferFromAssignSrc evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFrom_dst_checkedAdd_revert (transferFromAfterSrcDebitState evm I) I
        hover))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromBodyReverts_dstOverflow_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1)
    (hover : UInt256.size ≤ transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I) :
    ExecTransitionBody config contract evm (transferFromStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromStore I } evm)
      (evalExpr_transferFrom_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFrom_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFrom_src_debit evm I hsrcEnough)
      (transferFromAssignSrc evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFrom_dst_checkedAdd_revert (transferFromAfterSrcDebitState evm I) I
        hover))

/-! ## Source-level body for internal `transferFrom` calls -/

theorem transferFromCallStore_allowance (I : ExecutionEnv) :
    (transferFromCallStore I).get? "allowance" = none := by
  unfold transferFromCallStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem transferFromCallStore_balanceOf (I : ExecutionEnv) :
    (transferFromCallStore I).get? "balanceOf" = none := by
  unfold transferFromCallStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem transferFromCallStore_index_src (I : ExecutionEnv) :
    (transferFromCallStore I)["src"] = transferFromSrcValue I := by
  unfold transferFromCallStore
  simp [Std.HashMap.getElem_insert]

theorem transferFromCallStore_index_dst (I : ExecutionEnv) :
    (transferFromCallStore I)["dst"] = transferFromDstValue I := by
  unfold transferFromCallStore
  simp [Std.HashMap.getElem_insert]

theorem evalExpr_transferFromCall_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.var "wad") = .ok (transferFromWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromCallStore_get_wad]

theorem evalExpr_transferFromCall_src (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.var "src") = .ok (transferFromSrcValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromCallStore_get_src]

theorem evalExpr_transferFromCall_dst (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.var "dst") = .ok (transferFromDstValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferFromCallStore_get_dst]

theorem evalStorageRef_transferFromCall_src_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromCallStore I } evm
      (balanceOfRef (.var "src")) = .ok (transferFromSrcBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromSrcBalanceRef,
    transferFromSrcValue, transferFromSrcKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?, transferFromCallStore_index_src]

theorem evalStorageRef_transferFromCall_dst_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromCallStore I } evm
      (balanceOfRef (.var "dst")) = .ok (transferFromDstBalanceRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromDstBalanceRef,
    transferFromDstValue, transferFromDstKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?, transferFromCallStore_index_dst]

theorem evalStorageRef_transferFromCall_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferFromCallStore I } evm
      (allowanceRef (.var "src") sender) = .ok (transferFromAllowanceRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
    transferFromAllowanceRef, transferFromSrcValue, transferFromSrcKey,
    transferFromSpenderKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?, transferFromCallStore_index_src]

theorem evalExpr_transferFromCall_src_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.storage (balanceOfRef (.var "src"))) =
        .ok (transferFromSrcBalanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromCallStore I })
    (slot := balanceOfRef (.var "src"))
    (er := transferFromSrcBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromSrcSlot I) (.int uint256Int))
    (value := transferFromSrcBalanceValue evm I)
    (hbase := by
      simpa [balanceOfRef] using transferFromCallStore_balanceOf I)
    (her := evalStorageRef_transferFromCall_src_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
        uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromSrcBalanceWord] using
        storageLocLoad_uint256 evm (transferFromSrcSlot I))]

theorem evalExpr_transferFromCall_dst_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.storage (balanceOfRef (.var "dst"))) =
        .ok (transferFromDstBalanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromCallStore I })
    (slot := balanceOfRef (.var "dst"))
    (er := transferFromDstBalanceRef I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromDstSlot I) (.int uint256Int))
    (value := transferFromDstBalanceValue evm I)
    (hbase := by
      simpa [balanceOfRef] using transferFromCallStore_balanceOf I)
    (her := evalStorageRef_transferFromCall_dst_balance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromDstKey,
        uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromDstBalanceWord] using
        storageLocLoad_uint256 evm (transferFromDstSlot I))]

theorem evalExpr_transferFromCall_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.storage (allowanceRef (.var "src") sender)) =
        .ok (transferFromAllowanceValue evm I) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := transferFromCallStore I })
    (slot := allowanceRef (.var "src") sender)
    (er := transferFromAllowanceRef evm I)
    (t := .int uint256Int)
    (loc := wordLoc (transferFromAllowanceSlot evm I) (.int uint256Int))
    (value := transferFromAllowanceValue evm I)
    (hbase := by
      simpa [allowanceRef] using transferFromCallStore_allowance I)
    (her := evalStorageRef_transferFromCall_allowance evm I)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
        transferFromSpenderKey, uint256St])
    (hloc := by rfl)
    (hload := by
      simpa [wordLoc, uint256Loc, uint256Int, transferFromAllowanceWord] using
        storageLocLoad_uint256 evm (transferFromAllowanceSlot evm I))]

theorem evalExpr_transferFromCall_src_balance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_balance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue,
    transferFromWadValue, henough]

theorem evalExpr_transferFromCall_src_balance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromSrcBalanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_balance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue,
    transferFromWadValue]
  omega

theorem evalExpr_transferFromCall_allowance_ge_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?, henough]

theorem evalExpr_transferFromCall_allowance_ge_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromAllowanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem evalExpr_transferFromCall_src_ne_sender_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue,
    transferFromSrcValue, hne]

theorem evalExpr_transferFromCall_src_ne_sender_false (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue,
    transferFromSrcValue, heq]

theorem evalExpr_transferFromCall_allowance_ne_max_true (evm : EVM.State) (I : ExecutionEnv)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
        .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance]
  rw [show evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue, maxUint256]
  intro h
  apply hnotMax
  apply Int.ofNat.inj
  have hmaxInt : Int.ofNat (UInt256.size - 1) =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Int) := by
    norm_num [UInt256.size]
  rw [hmaxInt]
  exact h

theorem evalExpr_transferFromCall_allowance_ne_max_false (evm : EVM.State) (I : ExecutionEnv)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
        .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance]
  rw [show evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.intLit maxUint256) = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue, maxUint256,
    UInt256.size, hmax]

theorem evalExpr_transferFromCall_allowanceNeedsSpend_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool true) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_transferFromCall_allowance_ne_max_true evm I hnotMax]

theorem evalExpr_transferFromCall_allowanceNeedsSpend_false_sender
    (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_ne_sender_false evm I heq]
  simp only [EvalResult.bind, bind, evalExpr?, pure]

theorem evalExpr_transferFromCall_allowanceNeedsSpend_false_max (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (allowanceNeedsSpend (.var "src") sender) = .ok (.bool false) := by
  unfold allowanceNeedsSpend
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_ne_sender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_transferFromCall_allowance_ne_max_false evm I hmax]

theorem evalExpr_transferFromCall_allowance_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromAllowanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_allowance_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (sub256 (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromAllowanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat =
        Int.ofNat ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromAllowanceWord evm I).val.isLt)
  have hltNat :
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (transferFromAllowanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) ≥
      (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg : ¬
      (Int.ofNat ((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound : ¬
      115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFromCall_src_sub_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromSrcBalanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_balance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_src_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (sub256 (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromSrcDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromSrcBalanceWord evm I).toNat -
          Int.ofNat (transferFromWadWord I).toNat =
        Int.ofNat ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferFromSrcDebitWord evm I).toNat =
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromSrcDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (transferFromSrcBalanceWord evm I).val.isLt)
  have hltNat :
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sub_le _ _) (by
      simpa [UInt256.toNat, UInt256.size] using (transferFromSrcBalanceWord evm I).val.isLt)
  have hlt : ¬ Int.ofNat
        ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) ≥
      (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr hltNat)
  have hnotNeg : ¬
      (Int.ofNat ((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) < 0) := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  have hnotBound : ¬
      115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤
        (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    exact Nat.not_le_of_lt (by simpa using hltNat)
  conv_lhs =>
    unfold sub256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFromCall_src_sub_raw, hsub]
  simp [EvalResult.bind, bind, pure, uint256Int, hlt, hnotNeg, hnotBound]
  by_cases hnegGuard :
      (↑((transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat) : Int) < 0
  · exact False.elim (hnotNeg hnegGuard)
  · rw [if_neg hnegGuard]
    rw [htoNat]

theorem evalExpr_transferFromCall_dst_add_raw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
        .ok (.int (Int.ofNat (transferFromDstBalanceWord evm I).toNat +
          Int.ofNat (transferFromWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_dst_balance, evalExpr_transferFromCall_wad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_dst_credit (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
        .ok (transferFromDstCreditValue evm I) := by
  have hlt : ¬ Int.ofNat (transferFromDstCreditNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFromCall_dst_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromWadValue, transferFromDstCreditValue, transferFromDstCreditNat, uint256Int,
    hlt]
  constructor
  · omega
  · have hfitNat :
        (transferFromDstBalanceWord evm I).toNat + (transferFromWadWord I).toNat < 2 ^ 256 := by
      simpa [transferFromDstCreditNat, UInt256.size] using hfit
    omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_allowance_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .le (sub256 (.storage (allowanceRef (.var "src") sender)) (.var "wad"))
        (.storage (allowanceRef (.var "src") sender))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_allowance_debit evm I henough, evalExpr_transferFromCall_allowance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromAllowanceValue]
  have hdebit : (transferFromAllowanceDebitWord evm I).toNat =
      (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromAllowanceDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (transferFromAllowanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_src_checkedSub_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .le (sub256 (.storage (balanceOfRef (.var "src"))) (.var "wad"))
        (.storage (balanceOfRef (.var "src")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_src_debit evm I henough, evalExpr_transferFromCall_src_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromSrcBalanceValue]
  have hdebit : (transferFromSrcDebitWord evm I).toNat =
      (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat := by
    unfold transferFromSrcDebitWord
    exact ulit_toNat' _ (by
      have hlt :
          (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat < 2 ^ 256 := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) (by
          simpa [UInt256.toNat, UInt256.size] using (transferFromSrcBalanceWord evm I).val.isLt)
      simpa [UInt256.size] using hlt)
  omega

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_dst_checkedAdd_true (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad"))
        (.storage (balanceOfRef (.var "dst")))) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_dst_credit evm I hfit, evalExpr_transferFromCall_dst_balance]
  simp [EvalResult.bind, bind, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromDstCreditValue, transferFromDstCreditNat]

set_option maxHeartbeats 1000000 in
theorem evalExpr_transferFromCall_dst_credit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromDstCreditNat evm I) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad")) = .revert := by
  have hge : (2 : Int) ^ 256 ≤ Int.ofNat (transferFromDstCreditNat evm I) := by
    exact Int.ofNat_le.mpr (by simpa [UInt256.size] using hover)
  have hnotNeg : ¬ Int.ofNat (transferFromDstCreditNat evm I) < 0 := by
    exact not_lt_of_ge (Int.natCast_nonneg _)
  conv_lhs =>
    unfold add256
    unfold u256
    unfold evalExpr?
  rw [evalExpr_transferFromCall_dst_add_raw]
  simp [EvalResult.bind, bind, pure, evalBinaryOp?, transferFromDstBalanceValue,
    transferFromWadValue, transferFromDstCreditNat, uint256Int, hnotNeg, hge]
  intro _
  simpa [transferFromDstCreditNat] using hge

theorem evalExpr_transferFromCall_dst_checkedAdd_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferFromDstCreditNat evm I) :
    evalExpr? config { contract := contract, locals := transferFromCallStore I } evm
      (.binary .ge (add256 (.storage (balanceOfRef (.var "dst"))) (.var "wad"))
        (.storage (balanceOfRef (.var "dst")))) = .revert := by
  conv_lhs => unfold evalExpr?
  rw [evalExpr_transferFromCall_dst_credit_revert evm I hover]
  simp [EvalResult.bind, bind]

theorem transferFromCallAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromCallStore I } evm
      .storage (allowanceRef (.var "src") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromCallStore I },
          transferFromAfterAllowanceState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := allowanceRef (.var "src") sender)
      (er := transferFromAllowanceRef evm I)
      (ty := uint256St)
      (loc := wordLoc (transferFromAllowanceSlot evm I) (.int uint256Int))
      (hbase := by
        simpa [allowanceRef] using transferFromCallStore_allowance I)
      (her := evalStorageRef_transferFromCall_allowance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          transferFromSpenderKey, uint256St])
      (hloc := by rfl)
  rw [show wordLoc (transferFromAllowanceSlot evm I) (ElemType.int uint256Int) =
    uint256Loc (transferFromAllowanceSlot evm I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem transferFromCallAssignSrc (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromCallStore I } evm
      .storage (balanceOfRef (.var "src"))
      (.int (Int.ofNat (transferFromSrcDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromCallStore I },
          transferFromAfterSrcDebitState evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "src"))
      (er := transferFromSrcBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (transferFromSrcSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using transferFromCallStore_balanceOf I)
      (her := evalStorageRef_transferFromCall_src_balance evm I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          uint256St])
      (hloc := by rfl)
  rw [show wordLoc (transferFromSrcSlot I) (ElemType.int uint256Int) =
    uint256Loc (transferFromSrcSlot I) by rfl]
  rw [storageLocStore_uint256]
  rfl

theorem transferFromCallAssignDst (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferFromCallStore I }
      (transferFromAfterSrcDebitState evm I) .storage (balanceOfRef (.var "dst"))
      (transferFromDstCreditValue (transferFromAfterSrcDebitState evm I) I) =
        .ok ({ contract := contract, locals := transferFromCallStore I },
          transferFromPostStateFrom evm I) := by
  apply assignStorageRef_storage_scalar
      (slot := balanceOfRef (.var "dst"))
      (er := transferFromDstBalanceRef I)
      (ty := uint256St)
      (loc := wordLoc (transferFromDstSlot I) (.int uint256Int))
      (hbase := by
        simpa [balanceOfRef] using transferFromCallStore_balanceOf I)
      (her := evalStorageRef_transferFromCall_dst_balance (transferFromAfterSrcDebitState evm I) I)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromDstKey,
          uint256St])
      (hloc := by rfl)
  rw [← transferFromDstCreditWord_toNat (transferFromAfterSrcDebitState evm I) I hfit]
  rw [show wordLoc (transferFromDstSlot I) (ElemType.int uint256Int) =
    uint256Loc (transferFromDstSlot I) by rfl]
  rw [storageLocStore_uint256]
  simp only [transferFromPostStateFrom, transferFromAfterSrcDebit_codeOwner]

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReturns_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hsrcDebitEnough : (transferFromWadWord I).toNat ≤
      (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hfit : transferFromDstCreditNat
      (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromCallStore I }
        (transferFromPostStateFrom (transferFromAfterAllowanceState evm I) I)
        (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromCallStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFromCall_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFromCall_allowance_debit evm I hallowEnough)
        (transferFromCallAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFromCall_src_balance_ge_true (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFromCall_src_checkedSub_true (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_transferFromCall_src_debit (transferFromAfterAllowanceState evm I) I
          hsrcDebitEnough)
        (transferFromCallAssignSrc (transferFromAfterAllowanceState evm I) I)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_transferFromCall_dst_checkedAdd_true
          (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_transferFromCall_dst_credit
          (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hfit)
        (transferFromCallAssignDst (transferFromAfterAllowanceState evm I) I hfit)) ?_
    exact ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReturns_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromCallStore I }
        (transferFromPostStateFrom evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromCallStore I } evm)
      (evalExpr_transferFromCall_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFromCall_src_debit evm I hsrcEnough)
      (transferFromCallAssignSrc evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFromCall_dst_checkedAdd_true (transferFromAfterSrcDebitState evm I) I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFromCall_dst_credit (transferFromAfterSrcDebitState evm I) I hfit)
      (transferFromCallAssignDst evm I hfit)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReturns_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      (.returned { contract := contract, locals := transferFromCallStore I }
        (transferFromPostStateFrom evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromCallStore I } evm)
      (evalExpr_transferFromCall_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFromCall_src_debit evm I hsrcEnough)
      (transferFromCallAssignSrc evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFromCall_dst_checkedAdd_true (transferFromAfterSrcDebitState evm I) I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFromCall_dst_credit (transferFromAfterSrcDebitState evm I) I hfit)
      (transferFromCallAssignDst evm I hfit)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_initialBalance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromSrcBalanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transferFromCall_src_balance_ge_false evm I hlt))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromAllowanceWord evm I).toNat < (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue
      (result := .reverted)
      (evalExpr_transferFromCall_allowanceNeedsSpend_true evm I hne hnotMax)
      (ExecBlock.consRevert
        (ExecStmt.requireFalse (evalExpr_transferFromCall_allowance_ge_false evm I hlt))))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_srcDebit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hltDebit : (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat <
      (transferFromWadWord I).toNat) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromCallStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFromCall_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFromCall_allowance_debit evm I hallowEnough)
        (transferFromCallAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_transferFromCall_src_balance_ge_false (transferFromAfterAllowanceState evm I) I
        hltDebit))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_dstOverflow_spend (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (transferFromAllowanceWord evm I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat)
    (hsrcDebitEnough : (transferFromWadWord I).toNat ≤
      (transferFromSrcBalanceWord (transferFromAfterAllowanceState evm I) I).toNat)
    (hover : UInt256.size ≤ transferFromDstCreditNat
      (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteTrue
      (result := .ok { contract := contract, locals := transferFromCallStore I }
        (transferFromAfterAllowanceState evm I))
      (evalExpr_transferFromCall_allowanceNeedsSpend_true evm I hne hnotMax) ?_) ?_
  · refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_ge_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_transferFromCall_allowance_checkedSub_true evm I hallowEnough)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_transferFromCall_allowance_debit evm I hallowEnough)
        (transferFromCallAssignAllowance evm I)) ?_
    exact ExecBlock.nil
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFromCall_src_balance_ge_true (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_transferFromCall_src_checkedSub_true (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_transferFromCall_src_debit (transferFromAfterAllowanceState evm I) I
        hsrcDebitEnough)
      (transferFromCallAssignSrc (transferFromAfterAllowanceState evm I) I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFromCall_dst_checkedAdd_revert
        (transferFromAfterSrcDebitState (transferFromAfterAllowanceState evm I) I) I hover))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_dstOverflow_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (heq : AccountAddress.ofNat (transferFromSrcWord I).toNat = evm.executionEnv.source)
    (hover : UInt256.size ≤ transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromCallStore I } evm)
      (evalExpr_transferFromCall_allowanceNeedsSpend_false_sender evm I heq) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFromCall_src_debit evm I hsrcEnough)
      (transferFromCallAssignSrc evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFromCall_dst_checkedAdd_revert (transferFromAfterSrcDebitState evm I) I
        hover))

set_option maxHeartbeats 1000000 in
theorem daiTransferFromCallBodyReverts_dstOverflow_skipMax (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrcEnough : (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat)
    (hne : AccountAddress.ofNat (transferFromSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (transferFromAllowanceWord evm I).toNat = UInt256.size - 1)
    (hover : UInt256.size ≤ transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I) :
    ExecTransitionBody config contract evm (transferFromCallStore I) transferFromTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, spendAllowance, debitBalance, creditBalance,
    checkedSub, checkedAdd, List.append_assoc, List.nil_append, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (result := .ok { contract := contract, locals := transferFromCallStore I } evm)
      (evalExpr_transferFromCall_allowanceNeedsSpend_false_max evm I hne hmax) ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_balance_ge_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transferFromCall_src_checkedSub_true evm I hsrcEnough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transferFromCall_src_debit evm I hsrcEnough)
      (transferFromCallAssignSrc evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireRevert
      (evalExpr_transferFromCall_dst_checkedAdd_revert (transferFromAfterSrcDebitState evm I) I
        hover))


set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_initialBalanceOkCont {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (henough :
      (transferFromWadWord I).toNat ≤
        (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1411⟩
      (transferFromWadWord I :: transferFromDstMaskedWord I :: transferFromSrcMaskedWord I ::
        ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromSrcHashMem I).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨2⟩ := by
    simpa [transferFromSrcHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I)
        solcFreePtrMem_size
  have hmaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (transferFromSrcHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [transferFromSrcHashMem, solcSlotWord] using rdLoadedRaw
  have hgt :
      UInt256.gt (transferFromWadWord I)
          (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)) =
        ⟨0⟩ :=
    ugt_zero henough
  have rdGt := evm_run rdLoaded with [
    raw dup3 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdIszero := evm_run rdGt with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdIszero
  have rdPush := evm_run rdIszero with [raw push2 ⟨1515⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_initialBalanceOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (henough :
      (transferFromWadWord I).toNat ≤
        (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)).toNat)
    (h : RD daiBytecode I g s0 ⟨1411⟩
      [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨496⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiTransferFromX_initialBalanceOkCont (I := I) (ret := ⟨496⟩) (S := [sel])
    henough (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

theorem transferFromInsufficientBalanceWord :
    UInt256.shiftLeft
        (⟨0x4461692f696e73756666696369656e742d62616c616e6365⟩ : UInt256) ⟨64⟩ =
      ⟨0x4461692f696e73756666696369656e742d62616c616e63650000000000000000⟩ := by
  native_decide

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_initialBalanceRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hlt :
      (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)).toNat <
        (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1411⟩
      (transferFromWadWord I :: transferFromDstMaskedWord I :: transferFromSrcMaskedWord I ::
        ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromSrcHashMem I).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨2⟩ := by
    simpa [transferFromSrcHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I)
        solcFreePtrMem_size
  have hmaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hmaskLiteral] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (transferFromSrcHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [transferFromSrcHashMem, solcSlotWord] using rdLoadedRaw
  have hgt :
      UInt256.gt (transferFromWadWord I)
          (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)) =
        ⟨1⟩ :=
    ugt_one hlt
  have rdGt := evm_run rdLoaded with [
    raw dup3 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdIszero := evm_run rdGt with [raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdIszero
  have rdPush := evm_run rdIszero with [raw push2 ⟨1515⟩ (by native_decide) (by evm_ov)]
  have rdTail := rdPush.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1444⟩)
    (len := ⟨24⟩)
    (rawWord := ⟨0x4461692f696e73756666696369656e742d62616c616e6365⟩)
    (shift := ⟨64⟩)
    (word := ⟨0x4461692f696e73756666696369656e742d62616c616e63650000000000000000⟩)
    (op := .PUSH24)
    (width := 24)
    rdTail
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    transferFromInsufficientBalanceWord
    (transferFromSrcHashMem_size I)
    (transferFromSrcHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_initialBalanceRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hlt :
      (solcSlotWord σ I (mapSlot (transferFromSrcMaskedWord I) ⟨2⟩)).toNat <
        (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1411⟩
      [transferFromWadWord I, transferFromDstMaskedWord I, transferFromSrcMaskedWord I,
        ⟨496⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiTransferFromX_initialBalanceRevertCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hlt (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSkipSenderCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have heqWord :
      UInt256.eq (solcSourceWord I) (transferFromSrcMaskedWord I) = ⟨1⟩ := by
    rw [heq]
    exact u256_eq_refl (solcSourceWord I)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdMasked
  have rdEq := evm_run rdMasked with [
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [heqWord] at rdEq
  have rdCond := evm_run rdEq with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨1577⟩ (by native_decide) (by evm_ov)]
  have rd1577 := rdCond.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)
  have rdNeedFalse := evm_run rd1577 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by native_decide]
    at rdNeedFalse
  have rdPush := evm_run rdNeedFalse with [raw push2 ⟨1785⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSkipSender {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiTransferFromX_allowanceSkipSenderCont (I := I) (ret := ⟨496⟩) (S := [sel])
    heq (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceLoadedCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1577⟩
      ((UInt256.isZero (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256))
          (transferFromEvmAllowanceWord σ I)))
        :: ⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
          transferFromSrcMaskedWord I :: ret :: S)
      (transferFromAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have heqZero :
      UInt256.eq (solcSourceWord I) (transferFromSrcMaskedWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hne hbad.symm)
  have rdMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdMasked
  have rdEq := evm_run rdMasked with [
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [heqZero] at rdEq
  have rdCond := evm_run rdEq with [
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨1577⟩ (by native_decide) (by evm_ov)]
  have rdFall := rdCond.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoadStart := evm_run rdFall with [raw pop (by native_decide) (by evm_ov)]
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
            (transferFromSrcHashMem I)).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (transferFromSrcMaskedWord I)
        (transferFromSrcHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromAllowanceHashMem I).readWithPadding 0 64))) =
        transferFromEvmAllowanceSlot I := by
    unfold transferFromAllowanceHashMem solcNestedMappingCallerHashMem
    simpa [transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
          (transferFromSrcHashMem_size I))
  have rdLoadMasked := evm_run rdLoadStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdLoadMasked
  have rdInnerKeyPrefix := evm_run rdLoadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) (transferFromSrcHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromSrcHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromSrcHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (transferFromAllowanceHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (transferFromEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdLoadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdLoaded := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot] using rdLoadedRaw
  have rdMaxCheck := evm_run rdLoaded with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [UInt256.lnot] using rdMaxCheck⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceLoaded {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1577⟩
      [UInt256.isZero (UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256))
          (transferFromEvmAllowanceWord σ I)),
        ⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiTransferFromX_allowanceLoadedCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hne (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSkipMaxCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiTransferFromX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hword : transferFromEvmAllowanceWord σ I = UInt256.lnot (⟨0⟩ : UInt256) := by
    apply u256_inj
    rw [hmax, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (transferFromEvmAllowanceWord σ I) = ⟨1⟩ := by
    rw [hword]
    exact u256_eq_refl (UInt256.lnot (⟨0⟩ : UInt256))
  rw [heqMax] at rdLoaded
  have rdNeedFalse := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by native_decide]
    at rdNeedFalse
  have rdPush := evm_run rdNeedFalse with [raw push2 ⟨1785⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rdPush.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSkipMax {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromAllowanceHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiTransferFromX_allowanceSkipMaxCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hne hmax (by simp only [List.length_cons, List.length_nil]; omega) (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSpendCheckOkCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1702⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromAllowanceReloadHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiTransferFromX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ transferFromEvmAllowanceWord σ I := by
    intro hword
    apply hnotMax
    rw [← hword, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (transferFromEvmAllowanceWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hneq
  rw [heqMax] at rdLoaded
  have rdNeedTrue := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ from by native_decide]
    at rdNeedTrue
  have rdPushSkip := evm_run rdNeedTrue with [raw push2 ⟨1785⟩ (by native_decide) (by evm_ov)]
  have rdCheckStart := rdPushSkip.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
            (transferFromAllowanceHashMem I)).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (transferFromSrcMaskedWord I)
        (transferFromAllowanceHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromAllowanceReloadHashMem I).readWithPadding 0 64))) =
        transferFromEvmAllowanceSlot I := by
    unfold transferFromAllowanceReloadHashMem solcNestedMappingCallerHashMem
    simpa [transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
          (transferFromAllowanceHashMem_size I))
  have rdReloadMasked := evm_run rdCheckStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) (transferFromAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0 (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromAllowanceHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (transferFromAllowanceReloadHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (transferFromEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot] using rdReloadedRaw
  have hgt :
      UInt256.gt (transferFromWadWord I) (transferFromEvmAllowanceWord σ I) = ⟨0⟩ :=
    ugt_zero hallowEnough
  have rdGt := evm_run rdReloaded with [
    raw dup3 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdOk := evm_run rdGt with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1702⟩ (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by native_decide] at rdOk
  exact ⟨_, _, rdOk.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceSpendCheckOk {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1702⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromAllowanceReloadHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact daiTransferFromX_allowanceSpendCheckOkCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hne hnotMax hallowEnough (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailSuccessJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem (transferFromTailDstStoreMem mem I) (transferFromWadWord I))
      (UInt256.ofNat 5) rdata (cA, transferFromEvmTailPostAccountMap σ I) k' C' := by
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hdstMaskLiteral :
      UInt256.land (transferFromDstMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromDstMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromDstMaskedWord_canonical I)
  have hsrcSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem).readWithPadding
            0 64))) =
        transferFromEvmSrcSlot I := by
    simpa [transferFromEvmSrcSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I) hmem
  have rdSrcMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdSrcMasked
  have rdSrcMstore0Prefix := evm_run rdSrcMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSrcKey := rdSrcMstore0Prefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcSlotPrefix := evm_run rdSrcKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdSrcHashMem := rdSrcSlotPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcHashPrefix := evm_run rdSrcHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSrcSlot := rdSrcHashPrefix.keccak256 0 (transferFromEvmSrcSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hsrcSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdSrcLoadedRaw⟩ := rdSrcSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSrcLoaded := by
    simpa [transferFromEvmTailSrcBalanceWord, transferFromEvmSrcSlot] using rdSrcLoadedRaw
  have rdSubRoutinePre := evm_run rdSrcLoaded with [
    raw push2 ⟨1820⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdSubRoutine := rdSubRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := transferFromEvmTailSrcBalanceWord σ I) (b := transferFromWadWord I)
    (ret := ⟨1820⟩)
    (R := ⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
      transferFromSrcMaskedWord I :: ret :: S)
    rdSubRoutine hsubWf hsrcEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSub := by
    simpa [transferFromEvmTailSrcDebitWord] using rdAfterSubRaw
  have rdSrcStoreMasked := evm_run rdAfterSub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdSrcStoreMasked
  have rdSrcStoreKeyPrefix := evm_run rdSrcStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSrcStoreKey := rdSrcStoreKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcStoreSlotPrefix := evm_run rdSrcStoreKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdSrcStoreMem := rdSrcStoreSlotPrefix.mstore 0 (transferFromTailSrcStoreMem mem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hsrcStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromTailSrcStoreMem mem I).readWithPadding 0 64))) =
        transferFromEvmSrcSlot I := by
    simpa [transferFromTailSrcStoreMem, transferFromEvmSrcSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)
  have rdSrcStoreHashPrefix := evm_run rdSrcStoreMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdSrcStoreSlot := rdSrcStoreHashPrefix.keccak256 0 (transferFromEvmSrcSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hsrcStoreSlot
    (by native_decide) (by evm_ov)
  have rdBeforeSrcSstore := evm_run rdSrcStoreSlot with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterSrcSstoreRaw⟩ := rdBeforeSrcSstore.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSrcSstore := by
    simpa [transferFromEvmTailAfterSrcAccountMap, transferFromEvmTailSrcDebitWord,
      transferFromEvmSrcSlot] using rdAfterSrcSstoreRaw
  have rdDstMasked := evm_run rdAfterSrcSstore with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hdstMaskLiteral] at rdDstMasked
  have rdDstLoadPrefix := evm_run rdDstMasked with [raw dup2 (by native_decide) (by evm_ov)]
  have rdDstLoadMem := rdDstLoadPrefix.mstore 0
    (wordAt0Mem (transferFromDstMaskedWord I) (transferFromTailSrcStoreMem mem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have htailSrcRead32 :
      (transferFromTailSrcStoreMem mem I).readWithPadding 32 32 =
        UInt256.toByteArray (⟨2⟩ : UInt256) := by
    exact twoWordHashMem_read32 (transferFromSrcMaskedWord I) ⟨2⟩
      (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)
  have hdstLoadSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem (transferFromDstMaskedWord I)
            (transferFromTailSrcStoreMem mem I)).readWithPadding 0 64))) =
        transferFromEvmDstSlot I := by
    simpa [transferFromEvmDstSlot, mapSlot] using
      wordAt0Mem_solcMappingSlot_of_read32 (transferFromDstMaskedWord I) (⟨2⟩ : UInt256)
        (transferFromTailSrcStoreMem_size I hmem) htailSrcRead32
  have rdDstSlot := rdDstLoadMem.keccak256 0 (transferFromEvmDstSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hdstLoadSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdDstLoadedRaw⟩ := rdDstSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDstLoaded := by
    simpa [transferFromEvmTailDstBalanceWord, transferFromEvmTailAfterSrcAccountMap,
      transferFromEvmDstSlot] using rdDstLoadedRaw
  have rdAddRoutinePre := evm_run rdDstLoaded with [
    raw push2 ⟨1867⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3982⟩ (by native_decide) (by evm_ov)]
  have rdAddRoutine := rdAddRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have haddWf : solcCheckedAddSuccessWf daiBytecode ⟨3982⟩ ⟨1399⟩ := by
    unfold solcCheckedAddSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterAddRaw⟩ := RD.solcCheckedAddSuccess
    (pc := ⟨3982⟩) (okPc := ⟨1399⟩)
    (a := transferFromEvmTailDstBalanceWord σ I) (b := transferFromWadWord I)
    (ret := ⟨1867⟩)
    (R := ⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
      transferFromSrcMaskedWord I :: ret :: S)
    rdAddRoutine haddWf hfit (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterAdd := by
    simpa [transferFromEvmTailDstCreditWord] using rdAfterAddRaw
  have rdDstStoreMasked := evm_run rdAfterAdd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hdstMaskLiteral] at rdDstStoreMasked
  have rdDstStoreKeyPrefix := evm_run rdDstStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdDstStoreKey := rdDstStoreKeyPrefix.mstore 0
    (wordAt0Mem (transferFromDstMaskedWord I)
      (wordAt0Mem (transferFromDstMaskedWord I) (transferFromTailSrcStoreMem mem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdDstStoreSlotPrefix := evm_run rdDstStoreKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdDstStoreMem := rdDstStoreSlotPrefix.mstore 0 (transferFromTailDstStoreMem mem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hdstStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromTailDstStoreMem mem I).readWithPadding 0 64))) =
        transferFromEvmDstSlot I := by
    simpa [transferFromTailDstStoreMem, transferFromEvmDstSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromDstMaskedWord I)
        (wordAt0Mem_size_96 (transferFromDstMaskedWord I)
          (transferFromTailSrcStoreMem_size I hmem))
  have rdDstStoreHashPrefix := evm_run rdDstStoreMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdDstStoreSlot := rdDstStoreHashPrefix.keccak256 0 (transferFromEvmDstSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hdstStoreSlot
    (by native_decide) (by evm_ov)
  have rdBeforeDstSstore := evm_run rdDstStoreSlot with [
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterDstSstoreRaw⟩ := rdBeforeDstSstore.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterDstSstore := by
    simpa [transferFromEvmTailPostAccountMap, transferFromEvmTailAfterSrcAccountMap,
      transferFromEvmTailDstCreditWord, transferFromEvmDstSlot] using rdAfterDstSstoreRaw
  exact daiTransferFromX_logAndJump (I := I) (ret := ret) (S := S)
    (scratch := transferFromTailDstStoreMem mem I)
    hperm
    (transferFromTailDstStoreMem_size I hmem)
    (transferFromTailDstStoreMem_read64 I hmem hread64)
    hSlen hretDest
    rdAfterDstSstore

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, transferFromEvmTailPostAccountMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd496⟩ := daiTransferFromX_tailSuccessJump
    (I := I) (ret := ⟨496⟩) (S := [sel])
    hperm hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) hsrcEnough hfit (by simpa using h)
  have hretWf : solcReturnBoolFromMemWf daiBytecode ⟨496⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool :
      UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by
    native_decide
  simpa [hbool, transferFromTailBoolReturnMem] using
    RD.solcReturnBoolFromMem rd496 hretWf
      (solcScratchReturnMem_mload64 (transferFromWadWord I)
        (transferFromTailDstStoreMem_size I hmem)
        (transferFromTailDstStoreMem_read64 I hmem hread64))
      (by rfl)
      (transferFromTailBoolReturnMem_mload64 I
        (transferFromTailDstStoreMem_size I hmem)
        (transferFromTailDstStoreMem_read64 I hmem hread64))
      (transferFromTailBoolReturnMem_read128 I (transferFromTailDstStoreMem_size I hmem))
      (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_spendSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hsrcDebitEnough :
      (transferFromWadWord I).toNat ≤
        (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat +
          (transferFromWadWord I).toNat <
        UInt256.size)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0
      (cA, transferFromEvmTailPostAccountMap (transferFromEvmAfterAllowanceAccountMap σ I) I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1702⟩ :=
    daiTransferFromX_allowanceSpendCheckOk (I := I) hne hnotMax hallowEnough h
  have rd1703 := evm_run rd1702 with [raw jumpdest (by native_decide) (by evm_ov)]
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
            (transferFromAllowanceReloadHashMem I)).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (transferFromSrcMaskedWord I)
        (transferFromAllowanceReloadHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromAllowanceStoreHashMem I).readWithPadding 0 64))) =
        transferFromEvmAllowanceSlot I := by
    unfold transferFromAllowanceStoreHashMem solcNestedMappingCallerHashMem
    simpa [transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
          (transferFromAllowanceReloadHashMem_size I))
  have rdReloadMasked := evm_run rd1703 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) (transferFromAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
      (transferFromAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
        (transferFromAllowanceReloadHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (transferFromAllowanceStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (transferFromEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot] using rdReloadedRaw
  have rdRoutineRaw := evm_run rdReloaded with [
    raw push2 ⟨1748⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rdRoutine := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot, mapSlot,
      solcMappingSlot] using rdRoutineRaw
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := transferFromEvmAllowanceWord σ I) (b := transferFromWadWord I)
    (ret := ⟨1748⟩)
    (R := [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
      transferFromSrcMaskedWord I, ⟨496⟩, sel])
    rdRoutine hsubWf hallowEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSub := by
    simpa [transferFromEvmAllowanceDebitWord] using rdAfterSubRaw
  have hstoreWf : solcNestedMappingCallerStoreMemWf daiBytecode ⟨1748⟩ ⟨3⟩ := by
    unfold solcNestedMappingCallerStoreMemWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rd1785Raw⟩ := RD.solcNestedMappingCallerStoreMem
    (pc := ⟨1748⟩) (baseSlot := ⟨3⟩)
    (newValue := transferFromEvmAllowanceDebitWord σ I)
    (discard := ⟨0⟩) (value := transferFromWadWord I)
    (aux := transferFromDstMaskedWord I) (owner := transferFromSrcMaskedWord I)
    (ret := ⟨496⟩) (R := [sel])
    rdAfterSub hstoreWf (transferFromAllowanceStoreHashMem_size I)
    hperm (transferFromSrcMaskedWord_canonical I)
    (by simp only [List.length_singleton]; omega)
  have rd1785 := by
    simpa [transferFromEvmAfterAllowanceAccountMap, transferFromEvmAllowanceDebitWord,
      transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot]
      using rd1785Raw
  exact daiTransferFromX_tailSuccess (I := I)
    (σ := transferFromEvmAfterAllowanceAccountMap σ I)
    (sel := sel) hperm
    (solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
      (transferFromAllowanceStoreHashMem_size I))
    (solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
      (transferFromAllowanceStoreHashMem_size I) (transferFromAllowanceStoreHashMem_read64 I))
    hsrcDebitEnough hfit rd1785

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_skipSenderSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, transferFromEvmTailPostAccountMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1785⟩ := daiTransferFromX_allowanceSkipSender (I := I) heq h
  exact daiTransferFromX_tailSuccess (I := I) (σ := σ) (sel := sel)
    hperm (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I)
    hsrcEnough hfit rd1785

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_skipMaxSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret daiBytecode g s0 (cA, transferFromEvmTailPostAccountMap σ I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1785⟩ := daiTransferFromX_allowanceSkipMax (I := I) hne hmax h
  exact daiTransferFromX_tailSuccess (I := I) (σ := σ) (sel := sel)
    hperm (transferFromAllowanceHashMem_size I) (transferFromAllowanceHashMem_read64 I)
    hsrcEnough hfit rd1785

abbrev transferFromInsufficientAllowanceWord : UInt256 :=
  ⟨0x4461692f696e73756666696369656e742d616c6c6f77616e6365000000000000⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_insufficientAllowanceTail {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1626⟩ stk mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨26⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨26⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst transferFromInsufficientAllowanceWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨26⟩ transferFromInsufficientAllowanceWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨26⟩ transferFromInsufficientAllowanceWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromEvmAllowanceWord σ I).toNat < (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rdLoaded⟩ :=
    daiTransferFromX_allowanceLoadedCont (I := I) (ret := ret) (S := S) hne hSlen h
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hneq : UInt256.lnot (⟨0⟩ : UInt256) ≠ transferFromEvmAllowanceWord σ I := by
    intro hword
    apply hnotMax
    rw [← hword, hlnot0]
  have heqMax :
      UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) (transferFromEvmAllowanceWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hneq
  rw [heqMax] at rdLoaded
  have rdNeedTrue := evm_run rdLoaded with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ from by native_decide]
    at rdNeedTrue
  have rdPushSkip := evm_run rdNeedTrue with [raw push2 ⟨1785⟩ (by native_decide) (by evm_ov)]
  have rdCheckStart := rdPushSkip.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
            (transferFromAllowanceHashMem I)).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (transferFromSrcMaskedWord I)
        (transferFromAllowanceHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromAllowanceReloadHashMem I).readWithPadding 0 64))) =
        transferFromEvmAllowanceSlot I := by
    unfold transferFromAllowanceReloadHashMem solcNestedMappingCallerHashMem
    simpa [transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
          (transferFromAllowanceHashMem_size I))
  have rdReloadMasked := evm_run rdCheckStart with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) (transferFromAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromAllowanceHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩ (transferFromAllowanceHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (transferFromAllowanceReloadHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (transferFromEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot] using rdReloadedRaw
  have hgt :
      UInt256.gt (transferFromWadWord I) (transferFromEvmAllowanceWord σ I) = ⟨1⟩ :=
    ugt_one hlt
  have rdGt := evm_run rdReloaded with [
    raw dup3 (by native_decide) (by evm_ov),
    raw gt (by native_decide) (by evm_ov)]
  rw [hgt] at rdGt
  have rdFail := evm_run rdGt with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1702⟩ (by native_decide) (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by native_decide] at rdFail
  have rdTail := rdFail.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact daiTransferFromX_insufficientAllowanceTail
    (I := I) (σ := σ)
    (transferFromAllowanceReloadHashMem_size I)
    (transferFromAllowanceReloadHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)
    rdTail

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_allowanceRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hlt : (transferFromEvmAllowanceWord σ I).toNat < (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiTransferFromX_allowanceRevertCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hne hnotMax hlt (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailSrcDebitRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hlt :
      (transferFromEvmTailSrcBalanceWord σ I).toNat < (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hsrcSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem).readWithPadding
            0 64))) =
        transferFromEvmSrcSlot I := by
    simpa [transferFromEvmSrcSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I) hmem
  have rdSrcMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdSrcMasked
  have rdSrcMstore0Prefix := evm_run rdSrcMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSrcKey := rdSrcMstore0Prefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcSlotPrefix := evm_run rdSrcKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdSrcHashMem := rdSrcSlotPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcHashPrefix := evm_run rdSrcHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSrcSlot := rdSrcHashPrefix.keccak256 0 (transferFromEvmSrcSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hsrcSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdSrcLoadedRaw⟩ := rdSrcSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSrcLoaded := by
    simpa [transferFromEvmTailSrcBalanceWord, transferFromEvmSrcSlot] using rdSrcLoadedRaw
  have rdSubRoutinePre := evm_run rdSrcLoaded with [
    raw push2 ⟨1820⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdSubRoutine := rdSubRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  rcases hsubWf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat :
      (UInt256.sub (transferFromEvmTailSrcBalanceWord σ I) (transferFromWadWord I)).toNat =
        UInt256.size + (transferFromEvmTailSrcBalanceWord σ I).toNat -
          (transferFromWadWord I).toNat :=
    usub_toNat_underflow hlt
  have hgt :
      UInt256.gt
          (UInt256.sub (transferFromEvmTailSrcBalanceWord σ I) (transferFromWadWord I))
          (transferFromEvmTailSrcBalanceWord σ I) =
        ⟨1⟩ := by
    show UInt256.fromBool
        (decide
          (UInt256.sub (transferFromEvmTailSrcBalanceWord σ I) (transferFromWadWord I) >
            transferFromEvmTailSrcBalanceWord σ I)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show
        (UInt256.sub (transferFromEvmTailSrcBalanceWord σ I) (transferFromWadWord I)).toNat >
          (transferFromEvmTailSrcBalanceWord σ I).toNat
      rw [hsubNat]
      have hb : (transferFromWadWord I).toNat < UInt256.size :=
        (transferFromWadWord I).val.isLt
      omega
  have rd6 := evm_run rdSubRoutine with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  rw [hgt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨1399⟩ hd8 (by evm_ov)]
  have rdTail := rdPush.jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdTail
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailSrcDebitRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} {mem rdata : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlt :
      (transferFromEvmTailSrcBalanceWord σ I).toNat < (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiTransferFromX_tailSrcDebitRevertCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hmem hread64 (by simp only [List.length_cons, List.length_nil]; omega)
    hlt (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailDstOverflowRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hdstMaskLiteral :
      UInt256.land (transferFromDstMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromDstMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromDstMaskedWord_canonical I)
  have hsrcSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem).readWithPadding
            0 64))) =
        transferFromEvmSrcSlot I := by
    simpa [transferFromEvmSrcSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I) hmem
  have rdSrcMasked := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdSrcMasked
  have rdSrcMstore0Prefix := evm_run rdSrcMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSrcKey := rdSrcMstore0Prefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcSlotPrefix := evm_run rdSrcKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdSrcHashMem := rdSrcSlotPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcHashPrefix := evm_run rdSrcHashMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdSrcSlot := rdSrcHashPrefix.keccak256 0 (transferFromEvmSrcSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hsrcSlot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdSrcLoadedRaw⟩ := rdSrcSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdSrcLoaded := by
    simpa [transferFromEvmTailSrcBalanceWord, transferFromEvmSrcSlot] using rdSrcLoadedRaw
  have rdSubRoutinePre := evm_run rdSrcLoaded with [
    raw push2 ⟨1820⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov)]
  have rdSubRoutine := rdSubRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := transferFromEvmTailSrcBalanceWord σ I) (b := transferFromWadWord I)
    (ret := ⟨1820⟩)
    (R := ⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
      transferFromSrcMaskedWord I :: ret :: S)
    rdSubRoutine hsubWf hsrcEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSub := by
    simpa [transferFromEvmTailSrcDebitWord] using rdAfterSubRaw
  have rdSrcStoreMasked := evm_run rdAfterSub with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdSrcStoreMasked
  have rdSrcStoreKeyPrefix := evm_run rdSrcStoreMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdSrcStoreKey := rdSrcStoreKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨2⟩ mem))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdSrcStoreSlotPrefix := evm_run rdSrcStoreKey with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rdSrcStoreMem := rdSrcStoreSlotPrefix.mstore 0 (transferFromTailSrcStoreMem mem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hsrcStoreSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromTailSrcStoreMem mem I).readWithPadding 0 64))) =
        transferFromEvmSrcSlot I := by
    simpa [transferFromTailSrcStoreMem, transferFromEvmSrcSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨2⟩ : UInt256) (transferFromSrcMaskedWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)
  have rdSrcStoreHashPrefix := evm_run rdSrcStoreMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov)]
  have rdSrcStoreSlot := rdSrcStoreHashPrefix.keccak256 0 (transferFromEvmSrcSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hsrcStoreSlot
    (by native_decide) (by evm_ov)
  have rdBeforeSrcSstore := evm_run rdSrcStoreSlot with [
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterSrcSstoreRaw⟩ := rdBeforeSrcSstore.sstore hperm
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSrcSstore := by
    simpa [transferFromEvmTailAfterSrcAccountMap, transferFromEvmTailSrcDebitWord,
      transferFromEvmSrcSlot] using rdAfterSrcSstoreRaw
  have rdDstMasked := evm_run rdAfterSrcSstore with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hdstMaskLiteral] at rdDstMasked
  have rdDstLoadPrefix := evm_run rdDstMasked with [raw dup2 (by native_decide) (by evm_ov)]
  have rdDstLoadMem := rdDstLoadPrefix.mstore 0
    (wordAt0Mem (transferFromDstMaskedWord I) (transferFromTailSrcStoreMem mem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have htailSrcRead32 :
      (transferFromTailSrcStoreMem mem I).readWithPadding 32 32 =
        UInt256.toByteArray (⟨2⟩ : UInt256) := by
    exact twoWordHashMem_read32 (transferFromSrcMaskedWord I) ⟨2⟩
      (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨2⟩ hmem)
  have hdstLoadSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((wordAt0Mem (transferFromDstMaskedWord I)
            (transferFromTailSrcStoreMem mem I)).readWithPadding 0 64))) =
        transferFromEvmDstSlot I := by
    simpa [transferFromEvmDstSlot, mapSlot] using
      wordAt0Mem_solcMappingSlot_of_read32 (transferFromDstMaskedWord I) (⟨2⟩ : UInt256)
        (transferFromTailSrcStoreMem_size I hmem) htailSrcRead32
  have rdDstSlot := rdDstLoadMem.keccak256 0 (transferFromEvmDstSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost hdstLoadSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdDstLoadedRaw⟩ := rdDstSlot.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdDstLoaded := by
    simpa [transferFromEvmTailDstBalanceWord, transferFromEvmTailAfterSrcAccountMap,
      transferFromEvmDstSlot] using rdDstLoadedRaw
  have rdAddRoutinePre := evm_run rdDstLoaded with [
    raw push2 ⟨1867⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3982⟩ (by native_decide) (by evm_ov)]
  have rdAddRoutine := rdAddRoutinePre.jump (by native_decide) (by jump_dest) (by evm_ov)
  have haddWf : solcCheckedAddSuccessWf daiBytecode ⟨3982⟩ ⟨1399⟩ := by
    unfold solcCheckedAddSuccessWf
    repeat' first | apply And.intro | native_decide
  rcases haddWf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        2 * UInt256.size := by
    have ha : (transferFromEvmTailDstBalanceWord σ I).toNat < UInt256.size :=
      (transferFromEvmTailDstBalanceWord σ I).val.isLt
    have hb : (transferFromWadWord I).toNat < UInt256.size :=
      (transferFromWadWord I).val.isLt
    omega
  have hmod :
      ((transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat) %
          UInt256.size =
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat -
          UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat :
      (transferFromEvmTailDstBalanceWord σ I + transferFromWadWord I).toNat =
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat -
          UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt :
      UInt256.lt (transferFromEvmTailDstBalanceWord σ I + transferFromWadWord I)
          (transferFromEvmTailDstBalanceWord σ I) =
        ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : (transferFromWadWord I).toNat < UInt256.size :=
      (transferFromWadWord I).val.isLt
    omega
  have rd6 := evm_run rdAddRoutine with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  rw [hlt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 ⟨1399⟩ hd8 (by evm_ov)]
  have rdTail := rdPush.jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rdTail
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_tailDstOverflowRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      mem (UInt256.ofNat 3) rdata (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  exact daiTransferFromX_tailDstOverflowRevertCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hperm hmem hread64 (by simp only [List.length_cons, List.length_nil]; omega)
    hsrcEnough hover (by simpa using h)

noncomputable abbrev transferFromAllowancePostStoreHashMem (I : ExecutionEnv) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceStoreHashMem I)

theorem transferFromAllowancePostStoreHashMem_size (I : ExecutionEnv) :
    (transferFromAllowancePostStoreHashMem I).size = 96 :=
  solcNestedMappingCallerHashMem_size_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceStoreHashMem_size I)

theorem transferFromAllowancePostStoreHashMem_read64 (I : ExecutionEnv) :
    (transferFromAllowancePostStoreHashMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  solcNestedMappingCallerHashMem_read64_96 ⟨3⟩ (transferFromSrcMaskedWord I) I
    (transferFromAllowanceStoreHashMem_size I) (transferFromAllowanceStoreHashMem_read64 I)

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_spendToTailCont {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromAllowancePostStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferFromEvmAfterAllowanceAccountMap σ I) k' C' := by
  obtain ⟨_, _, rd1702⟩ :=
    daiTransferFromX_allowanceSpendCheckOkCont (I := I) (ret := ret) (S := S)
      hne hnotMax hallowEnough hSlen h
  have rd1703 := evm_run rd1702 with [raw jumpdest (by native_decide) (by evm_ov)]
  have hsrcMaskLiteral :
      UInt256.land (transferFromSrcMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        transferFromSrcMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (transferFromSrcMaskedWord_canonical I)
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
            (transferFromAllowanceReloadHashMem I)).readWithPadding 0 64))) =
        mapSlot (transferFromSrcMaskedWord I) ⟨3⟩ := by
    simpa [mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨3⟩ : UInt256) (transferFromSrcMaskedWord I)
        (transferFromAllowanceReloadHashMem_size I)
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((transferFromAllowanceStoreHashMem I).readWithPadding 0 64))) =
        transferFromEvmAllowanceSlot I := by
    unfold transferFromAllowanceStoreHashMem solcNestedMappingCallerHashMem
    simpa [transferFromEvmAllowanceSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨3⟩ (transferFromSrcMaskedWord I))
        (solcSourceWord I)
        (twoWordHashMem_size_96 (transferFromSrcMaskedWord I) ⟨3⟩
          (transferFromAllowanceReloadHashMem_size I))
  have rdReloadMasked := evm_run rd1703 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  rw [hsrcMaskLiteral] at rdReloadMasked
  have rdInnerKeyPrefix := evm_run rdReloadMasked with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerKey := rdInnerKeyPrefix.mstore 0
    (wordAt0Mem (transferFromSrcMaskedWord I) (transferFromAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0
    (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
      (transferFromAllowanceReloadHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rdInnerHash := rdInnerHashPrefix.keccak256 0
    (mapSlot (transferFromSrcMaskedWord I) ⟨3⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hinnerSlot
    (by native_decide) (by evm_ov)
  have rdCaller := evm_run rdInnerHash with [
    raw caller (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rdOuterKey := rdCaller.mstore 0
    (wordAt0Mem (solcSourceWord I)
      (twoWordHashMem (transferFromSrcMaskedWord I) ⟨3⟩
        (transferFromAllowanceReloadHashMem I)))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0 (transferFromAllowanceStoreHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdOuterHashPrefix := evm_run rdOuterMem with [raw swap1 (by native_decide) (by evm_ov)]
  have rdOuterHash := rdOuterHashPrefix.keccak256 0 (transferFromEvmAllowanceSlot I)
    (UInt256.ofNat 3) (by native_decide) mem_cost houterSlot
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdReloadedRaw⟩ := rdOuterHash.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdReloaded := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot] using rdReloadedRaw
  have rdRoutineRaw := evm_run rdReloaded with [
    raw push2 ⟨1748⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨3966⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have rdRoutine := by
    simpa [transferFromEvmAllowanceWord, transferFromEvmAllowanceSlot, mapSlot,
      solcMappingSlot] using rdRoutineRaw
  have hsubWf : solcCheckedSubSuccessWf daiBytecode ⟨3966⟩ ⟨1399⟩ := by
    unfold solcCheckedSubSuccessWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdAfterSubRaw⟩ := RD.solcCheckedSubSuccess
    (pc := ⟨3966⟩) (okPc := ⟨1399⟩)
    (a := transferFromEvmAllowanceWord σ I) (b := transferFromWadWord I)
    (ret := ⟨1748⟩)
    (R := ⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
      transferFromSrcMaskedWord I :: ret :: S)
    rdRoutine hsubWf hallowEnough (by jump_dest) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdAfterSub := by
    simpa [transferFromEvmAllowanceDebitWord] using rdAfterSubRaw
  have hstoreWf : solcNestedMappingCallerStoreMemWf daiBytecode ⟨1748⟩ ⟨3⟩ := by
    unfold solcNestedMappingCallerStoreMemWf
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rd1785Raw⟩ := RD.solcNestedMappingCallerStoreMem
    (pc := ⟨1748⟩) (baseSlot := ⟨3⟩)
    (newValue := transferFromEvmAllowanceDebitWord σ I)
    (discard := ⟨0⟩) (value := transferFromWadWord I)
    (aux := transferFromDstMaskedWord I) (owner := transferFromSrcMaskedWord I)
    (ret := ret) (R := S)
    rdAfterSub hstoreWf (transferFromAllowanceStoreHashMem_size I)
    hperm (transferFromSrcMaskedWord_canonical I)
    (by omega)
  exact ⟨_, _, by
    simpa [transferFromEvmAfterAllowanceAccountMap, transferFromEvmAllowanceDebitWord,
      transferFromEvmAllowanceSlot, transferFromAllowancePostStoreHashMem, mapSlot,
      solcMappingSlot] using rd1785Raw⟩

set_option maxHeartbeats 1000000 in
theorem daiTransferFromX_spendToTail {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ⟨1785⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromAllowancePostStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, transferFromEvmAfterAllowanceAccountMap σ I) k' C' := by
  exact daiTransferFromX_spendToTailCont (I := I) (ret := ⟨496⟩) (S := [sel])
    hperm hne hnotMax hallowEnough
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by simpa using h)

theorem daiTransferFromX_skipSenderSuccessJump {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem (transferFromTailDstStoreMem (transferFromSrcHashMem I) I)
        (transferFromWadWord I))
      (UInt256.ofNat 5) ByteArray.empty (cA, transferFromEvmTailPostAccountMap σ I) k' C' := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_allowanceSkipSenderCont (I := I) (ret := ret) (S := S)
      heq hSlen h
  exact daiTransferFromX_tailSuccessJump (I := I) (σ := σ) (ret := ret) (S := S)
    hperm (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I)
    hSlen hretDest hsrcEnough hfit rd1785

theorem daiTransferFromX_skipMaxSuccessJump {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem (transferFromTailDstStoreMem (transferFromAllowanceHashMem I) I)
        (transferFromWadWord I))
      (UInt256.ofNat 5) ByteArray.empty (cA, transferFromEvmTailPostAccountMap σ I) k' C' := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_allowanceSkipMaxCont (I := I) (ret := ret) (S := S)
      hne hmax hSlen h
  exact daiTransferFromX_tailSuccessJump (I := I) (σ := σ) (ret := ret) (S := S)
    hperm (transferFromAllowanceHashMem_size I) (transferFromAllowanceHashMem_read64 I)
    hSlen hretDest hsrcEnough hfit rd1785

theorem daiTransferFromX_spendSuccessJump {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hsrcDebitEnough :
      (transferFromWadWord I).toNat ≤
        (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat +
          (transferFromWadWord I).toNat <
        UInt256.size)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiBytecode I g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem (transferFromTailDstStoreMem (transferFromAllowancePostStoreHashMem I) I)
        (transferFromWadWord I))
      (UInt256.ofNat 5) ByteArray.empty
      (cA, transferFromEvmTailPostAccountMap (transferFromEvmAfterAllowanceAccountMap σ I) I)
      k' C' := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_spendToTailCont (I := I) (ret := ret) (S := S)
      hperm hne hnotMax hallowEnough hSlen h
  exact daiTransferFromX_tailSuccessJump
    (I := I) (σ := transferFromEvmAfterAllowanceAccountMap σ I) (ret := ret) (S := S)
    hperm (transferFromAllowancePostStoreHashMem_size I)
    (transferFromAllowancePostStoreHashMem_read64 I)
    hSlen hretDest hsrcDebitEnough hfit rd1785

theorem daiTransferFromX_spendSrcDebitRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hltDebit :
      (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat <
        (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_spendToTail hperm hne hnotMax hallowEnough h
  exact daiTransferFromX_tailSrcDebitRevert
    (I := I) (σ := transferFromEvmAfterAllowanceAccountMap σ I)
    (sel := sel)
    (transferFromAllowancePostStoreHashMem_size I)
    (transferFromAllowancePostStoreHashMem_read64 I)
    hltDebit rd1785

theorem daiTransferFromX_spendDstOverflowRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hsrcDebitEnough :
      (transferFromWadWord I).toNat ≤
        (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat +
          (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_spendToTail hperm hne hnotMax hallowEnough h
  exact daiTransferFromX_tailDstOverflowRevert
    (I := I) (σ := transferFromEvmAfterAllowanceAccountMap σ I)
    (sel := sel) hperm
    (transferFromAllowancePostStoreHashMem_size I)
    (transferFromAllowancePostStoreHashMem_read64 I)
    hsrcDebitEnough hover rd1785

theorem daiTransferFromX_skipSenderDstOverflowRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ := daiTransferFromX_allowanceSkipSender (I := I) heq h
  exact daiTransferFromX_tailDstOverflowRevert (I := I) (σ := σ) (sel := sel)
    hperm (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I)
    hsrcEnough hover rd1785

theorem daiTransferFromX_skipMaxDstOverflowRevert {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      [⟨0⟩, transferFromWadWord I, transferFromDstMaskedWord I,
        transferFromSrcMaskedWord I, ⟨496⟩, sel]
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ := daiTransferFromX_allowanceSkipMax (I := I) hne hmax h
  exact daiTransferFromX_tailDstOverflowRevert (I := I) (σ := σ) (sel := sel)
    hperm (transferFromAllowanceHashMem_size I) (transferFromAllowanceHashMem_read64 I)
    hsrcEnough hover rd1785

theorem daiTransferFromX_spendSrcDebitRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hltDebit :
      (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat <
        (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_spendToTailCont (I := I) (ret := ret) (S := S)
      hperm hne hnotMax hallowEnough hSlen h
  exact daiTransferFromX_tailSrcDebitRevertCont
    (I := I) (σ := transferFromEvmAfterAllowanceAccountMap σ I) (ret := ret) (S := S)
    (transferFromAllowancePostStoreHashMem_size I)
    (transferFromAllowancePostStoreHashMem_read64 I)
    hSlen hltDebit rd1785

theorem daiTransferFromX_spendDstOverflowRevertCont {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hnotMax : (transferFromEvmAllowanceWord σ I).toNat ≠ UInt256.size - 1)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat)
    (hsrcDebitEnough :
      (transferFromWadWord I).toNat ≤
        (transferFromEvmTailSrcBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord (transferFromEvmAfterAllowanceAccountMap σ I) I).toNat +
          (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_spendToTailCont (I := I) (ret := ret) (S := S)
      hperm hne hnotMax hallowEnough hSlen h
  exact daiTransferFromX_tailDstOverflowRevertCont
    (I := I) (σ := transferFromEvmAfterAllowanceAccountMap σ I) (ret := ret) (S := S)
    hperm (transferFromAllowancePostStoreHashMem_size I)
    (transferFromAllowancePostStoreHashMem_read64 I)
    hSlen hsrcDebitEnough hover rd1785

theorem daiTransferFromX_skipSenderDstOverflowRevertCont {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (heq : transferFromSrcMaskedWord I = solcSourceWord I)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_allowanceSkipSenderCont (I := I) (ret := ret) (S := S)
      heq hSlen h
  exact daiTransferFromX_tailDstOverflowRevertCont (I := I) (σ := σ) (ret := ret) (S := S)
    hperm (transferFromSrcHashMem_size I) (transferFromSrcHashMem_read64 I)
    hSlen hsrcEnough hover rd1785

theorem daiTransferFromX_skipMaxDstOverflowRevertCont {cA σ I} {g : Sat256}
    {s0 : State} {k C : ℕ} {ret : UInt256} {S : List UInt256}
    (hperm : I.perm = true)
    (hne : transferFromSrcMaskedWord I ≠ solcSourceWord I)
    (hmax : (transferFromEvmAllowanceWord σ I).toNat = UInt256.size - 1)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hover :
      UInt256.size ≤
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat)
    (hSlen : S.length + 16 ≤ 1024)
    (h : RD daiBytecode I g s0 ⟨1515⟩
      (⟨0⟩ :: transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      (transferFromSrcHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiBytecode g s0 := by
  obtain ⟨_, _, rd1785⟩ :=
    daiTransferFromX_allowanceSkipMaxCont (I := I) (ret := ret) (S := S)
      hne hmax hSlen h
  exact daiTransferFromX_tailDstOverflowRevertCont (I := I) (σ := σ) (ret := ret) (S := S)
    hperm (transferFromAllowanceHashMem_size I) (transferFromAllowanceHashMem_read64 I)
    hSlen hsrcEnough hover rd1785

theorem transferFromAllowanceWord_accountMapEquiv {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evm.executionEnv.source = I.source)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    transferFromEvmAllowanceWord σ I = transferFromAllowanceWord evm I := by
  have hread :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (transferFromEvmAllowanceSlot I)
      (⟨0⟩ : UInt256)
  unfold transferFromAllowanceWord
  rw [show transferFromAllowanceSlot evm I = transferFromEvmAllowanceSlot I by
    simpa [transferFromEvmAllowanceSlot] using
      transferFromAllowanceSlot_eq_mapSlot_masked evm I hsource]
  simpa [transferFromEvmAllowanceWord, Solm.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, solcSlotWord, howner] using hread

theorem transferFromAfterAllowance_accountMapEquiv {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hsource : evm.executionEnv.source = I.source)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hallowEnough : (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ I).toNat) :
    accountMapEquiv (transferFromEvmAfterAllowanceAccountMap σ I)
      (transferFromAfterAllowanceState evm I).accountMap := by
  have hallowWord :=
    transferFromAllowanceWord_accountMapEquiv (σ := σ) (evm := evm) (I := I)
      howner hsource hAccounts
  have hallowDebitEq :
      transferFromEvmAllowanceDebitWord σ I = transferFromAllowanceDebitWord evm I := by
    apply u256_inj
    unfold transferFromEvmAllowanceDebitWord transferFromAllowanceDebitWord
    rw [usub_toNat hallowEnough]
    have hallowEnoughSolm :
        (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evm I).toNat := by
      rw [← hallowWord]
      exact hallowEnough
    have hlt :
        (transferFromAllowanceWord evm I).toNat - (transferFromWadWord I).toNat <
          UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (transferFromAllowanceWord evm I).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [← hallowWord]
  have hslot :
      transferFromAllowanceSlot evm I = transferFromEvmAllowanceSlot I := by
    simpa [transferFromEvmAllowanceSlot] using
      transferFromAllowanceSlot_eq_mapSlot_masked evm I hsource
  simpa [transferFromEvmAfterAllowanceAccountMap, transferFromAfterAllowanceState,
    storageStore_accountMap, howner, hslot, hallowDebitEq] using
    accountMapEquiv_sstoreAccountMap I.codeOwner (transferFromEvmAllowanceSlot I)
      (transferFromEvmAllowanceDebitWord σ I) hAccounts

set_option maxHeartbeats 1000000 in
theorem transferFromTailSolmPrefixBridge {σ : AccountMap} {evm : EVM.State}
    {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat) :
    (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat ∧
    transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I =
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat ∧
    accountMapEquiv (transferFromEvmTailAfterSrcAccountMap σ I)
      (transferFromAfterSrcDebitState evm I).accountMap := by
  have hsrcWord :
      transferFromEvmTailSrcBalanceWord σ I = transferFromSrcBalanceWord evm I := by
    have hread :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (transferFromEvmSrcSlot I)
        (⟨0⟩ : UInt256)
    simpa [transferFromEvmTailSrcBalanceWord, transferFromSrcBalanceWord,
      transferFromEvmSrcSlot, transferFromSrcSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, howner] using hread
  have hsrcEnoughSolm :
      (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat := by
    rw [← hsrcWord]
    exact hsrcEnough
  have hsrcDebitEq :
      transferFromEvmTailSrcDebitWord σ I = transferFromSrcDebitWord evm I := by
    apply u256_inj
    unfold transferFromEvmTailSrcDebitWord transferFromSrcDebitWord
    rw [usub_toNat hsrcEnough]
    have hlt :
        (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat <
          UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (transferFromSrcBalanceWord evm I).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [← hsrcWord]
  have hsrcMap :
      accountMapEquiv (transferFromEvmTailAfterSrcAccountMap σ I)
        (transferFromAfterSrcDebitState evm I).accountMap := by
    simpa [transferFromEvmTailAfterSrcAccountMap, transferFromAfterSrcDebitState,
      storageStore_accountMap, transferFromEvmSrcSlot, transferFromSrcSlot_eq_mapSlot_masked,
      howner, hsrcDebitEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (transferFromEvmSrcSlot I)
        (transferFromEvmTailSrcDebitWord σ I) hAccounts
  have hdstWord :
      transferFromEvmTailDstBalanceWord σ I =
        transferFromDstBalanceWord (transferFromAfterSrcDebitState evm I) I := by
    have hread :=
      accountMapEquiv_storage_findD hsrcMap I.codeOwner (transferFromEvmDstSlot I)
        (⟨0⟩ : UInt256)
    have hownerAfter :
        (transferFromAfterSrcDebitState evm I).executionEnv.codeOwner = I.codeOwner := by
      simpa [transferFromAfterSrcDebit_codeOwner evm I] using howner
    simpa [transferFromEvmTailDstBalanceWord, transferFromDstBalanceWord,
      transferFromEvmDstSlot, transferFromDstSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, hownerAfter] using hread
  have hcreditNat :
      transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I =
        (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat := by
    unfold transferFromDstCreditNat
    rw [← hdstWord]
  exact ⟨hsrcEnoughSolm, hcreditNat, hsrcMap⟩

set_option maxHeartbeats 1000000 in
theorem transferFromTailSolmBridge {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hAccounts : accountMapEquiv σ evm.accountMap)
    (hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ I).toNat)
    (hfit :
      (transferFromEvmTailDstBalanceWord σ I).toNat + (transferFromWadWord I).toNat <
        UInt256.size) :
    (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat ∧
    transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size ∧
    accountMapEquiv (transferFromEvmTailPostAccountMap σ I)
      (transferFromPostStateFrom evm I).accountMap := by
  have hsrcWord :
      transferFromEvmTailSrcBalanceWord σ I = transferFromSrcBalanceWord evm I := by
    have hread :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (transferFromEvmSrcSlot I)
        (⟨0⟩ : UInt256)
    simpa [transferFromEvmTailSrcBalanceWord, transferFromSrcBalanceWord,
      transferFromEvmSrcSlot, transferFromSrcSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, howner] using hread
  have hsrcEnoughSolm :
      (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evm I).toNat := by
    rw [← hsrcWord]
    exact hsrcEnough
  have hsrcDebitEq :
      transferFromEvmTailSrcDebitWord σ I = transferFromSrcDebitWord evm I := by
    apply u256_inj
    unfold transferFromEvmTailSrcDebitWord transferFromSrcDebitWord
    rw [usub_toNat hsrcEnough]
    have hlt :
        (transferFromSrcBalanceWord evm I).toNat - (transferFromWadWord I).toNat <
          UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (transferFromSrcBalanceWord evm I).val.isLt
    rw [ulit_toNat' _ hlt]
    rw [← hsrcWord]
  have hsrcMap :
      accountMapEquiv (transferFromEvmTailAfterSrcAccountMap σ I)
        (transferFromAfterSrcDebitState evm I).accountMap := by
    simpa [transferFromEvmTailAfterSrcAccountMap, transferFromAfterSrcDebitState,
      storageStore_accountMap, transferFromEvmSrcSlot, transferFromSrcSlot_eq_mapSlot_masked,
      howner, hsrcDebitEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (transferFromEvmSrcSlot I)
        (transferFromEvmTailSrcDebitWord σ I) hAccounts
  have hdstWord :
      transferFromEvmTailDstBalanceWord σ I =
        transferFromDstBalanceWord (transferFromAfterSrcDebitState evm I) I := by
    have hread :=
      accountMapEquiv_storage_findD hsrcMap I.codeOwner (transferFromEvmDstSlot I)
        (⟨0⟩ : UInt256)
    have hownerAfter :
        (transferFromAfterSrcDebitState evm I).executionEnv.codeOwner = I.codeOwner := by
      simpa [transferFromAfterSrcDebit_codeOwner evm I] using howner
    simpa [transferFromEvmTailDstBalanceWord, transferFromDstBalanceWord,
      transferFromEvmDstSlot, transferFromDstSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, solcSlotWord, hownerAfter] using hread
  have hfitSolm :
      transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size := by
    unfold transferFromDstCreditNat
    rw [← hdstWord]
    exact hfit
  have hcreditEq :
      transferFromEvmTailDstCreditWord σ I =
        transferFromDstCreditWord (transferFromAfterSrcDebitState evm I) I := by
    apply u256_inj
    unfold transferFromEvmTailDstCreditWord transferFromDstCreditWord transferFromDstCreditNat
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
    rw [ulit_toNat' _ (by simpa [transferFromDstCreditNat] using hfitSolm)]
    rw [← hdstWord]
  have hfinal :
      accountMapEquiv (transferFromEvmTailPostAccountMap σ I)
        (transferFromPostStateFrom evm I).accountMap := by
    simpa [transferFromEvmTailPostAccountMap, transferFromPostStateFrom,
      storageStore_accountMap, transferFromEvmDstSlot, transferFromDstSlot_eq_mapSlot_masked,
      howner, hcreditEq] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (transferFromEvmDstSlot I)
        (transferFromEvmTailDstCreditWord σ I) hsrcMap
  exact ⟨hsrcEnoughSolm, hfitSolm, hfinal⟩

theorem daiTransferFromBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some transferFromTransition)
    (hreach : ∃ k C, RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨542⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := daiDecode_transferFrom_none_short (I := I) hsz4 hshort
  exact (daiTransferFromX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

set_option maxHeartbeats 2000000 in
theorem daiTransferFromInternalCallRuntimeCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {t : TransitionDecl} {callargs : Store} {ret : UInt256} {S : List UInt256}
    {out : ByteArray} {retVal : Option (List Value)} {k C : ℕ}
    (hcode : I.code = daiBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some t)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = some callargs)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hSlen : S.length + 16 ≤ 1024)
    (hretDest : (D_J daiBytecode 0).contains ret = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (rd1411 : RD daiBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1411⟩
      (transferFromWadWord I :: transferFromDstMaskedWord I ::
        transferFromSrcMaskedWord I :: ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hfinish : ∀ {σ' scratch k' C'},
      scratch.size = 96 →
      scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ →
      RD daiBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ret (⟨1⟩ :: S)
        (solcScratchReturnMem scratch (transferFromWadWord I)) (UInt256.ofNat 5)
        ByteArray.empty (cA, σ') k' C' →
      RDret daiBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ') out)
    (hwrapReturn : ∀ {evmPost},
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (transferFromCallStore I) transferFromTransition.body
        (.returned { contract := contract, locals := transferFromCallStore I } evmPost
          (some [.bool true])) →
      ∃ cs, ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        callargs t.body (.returned cs evmPost retVal))
    (hwrapRevert :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (transferFromCallStore I) transferFromTransition.body .reverted →
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        callargs t.body .reverted)
    (henc : returnEquiv out retVal t.returnType) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hownerSolm : evmSolm.executionEnv.codeOwner = I.codeOwner := by
    simp [evmSolm, initState]
  have hsourceSolm : evmSolm.executionEnv.source = I.source := by
    simp [evmSolm, initState]
  have hsrcWord :
      transferFromEvmTailSrcBalanceWord σ_evm I =
        transferFromSrcBalanceWord evmSolm I := by
    rw [transferFromSrcBalanceWord_initState (σ := σ_solm)]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (transferFromEvmSrcSlot I) (⟨0⟩ : UInt256)
  by_cases hsrcEnough :
      (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ_evm I).toNat
  · obtain ⟨_, _, rd1515⟩ :=
      daiTransferFromX_initialBalanceOkCont
        (I := I) (ret := ret) (S := S) hsrcEnough hSlen rd1411
    have hsrcEnoughSolm :
        (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evmSolm I).toNat := by
      rw [← hsrcWord]
      exact hsrcEnough
    by_cases hsrcIsSender :
        AccountAddress.ofNat (transferFromSrcWord I).toNat = I.source
    · have heqWord :=
        transferFromSrcMaskedWord_eq_solcSourceWord_of_address_eq I hsrcIsSender
      by_cases hfit :
          (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
              (transferFromWadWord I).toNat < UInt256.size
      · rcases transferFromTailSolmBridge hownerSolm hAccounts hsrcEnough hfit with
          ⟨hsrcEnoughBody, hfitBody, hfinal⟩
        have hbodyTf :
            ExecTransitionBody config contract evmSolm (transferFromCallStore I)
              transferFromTransition.body
              (.returned { contract := contract, locals := transferFromCallStore I }
                (transferFromPostStateFrom evmSolm I) (some [.bool true])) := by
          simpa [evmSolm] using
            daiTransferFromCallBodyReturns_skipSender evmSolm I
              (by simp only [evmSolm, initState]; exact hwv)
              hsrcEnoughBody
              (by simpa [evmSolm, initState] using hsrcIsSender)
              hfitBody
        obtain ⟨cs, hbody⟩ := hwrapReturn (by simpa [evmSolm] using hbodyTf)
        obtain ⟨_, _, rdret⟩ :=
          daiTransferFromX_skipSenderSuccessJump
            (I := I) (σ := σ_evm) (ret := ret) (S := S)
            hperm heqWord hsrcEnough hfit hSlen hretDest rd1515
        have hrdret :=
          hfinish
            (transferFromTailDstStoreMem_size I (transferFromSrcHashMem_size I))
            (transferFromTailDstStoreMem_read64 I (transferFromSrcHashMem_size I)
              (transferFromSrcHashMem_read64 I))
            rdret
        exact hrdret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          (by
            simp [transferFromPostStateFrom, transferFromAfterSrcDebitState, evmSolm,
              initState, storageStore_createdAccounts])
          hfinal
          henc
      · have hover :
          UInt256.size ≤
            (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
              (transferFromWadWord I).toNat := by omega
        rcases transferFromTailSolmPrefixBridge hownerSolm hAccounts hsrcEnough with
          ⟨hsrcEnoughBody, hcreditNat, _⟩
        have hoverBody :
            UInt256.size ≤
              transferFromDstCreditNat (transferFromAfterSrcDebitState evmSolm I) I := by
          rw [hcreditNat]
          exact hover
        have hbodyTf :
            ExecTransitionBody config contract evmSolm (transferFromCallStore I)
              transferFromTransition.body .reverted := by
          simpa [evmSolm] using
            daiTransferFromCallBodyReverts_dstOverflow_skipSender evmSolm I
              (by simp only [evmSolm, initState]; exact hwv)
              hsrcEnoughBody
              (by simpa [evmSolm, initState] using hsrcIsSender)
              hoverBody
        exact
          (daiTransferFromX_skipSenderDstOverflowRevertCont
              (I := I) (σ := σ_evm) (ret := ret) (S := S)
              hperm heqWord hsrcEnough hover hSlen rd1515)
          |>.reEquivExecutionRevert hcode hdispatch hdecode
            (hwrapRevert (by simpa [evmSolm] using hbodyTf))
    · have hneWord : transferFromSrcMaskedWord I ≠ solcSourceWord I := by
        intro hbad
        exact hsrcIsSender (transferFrom_address_eq_of_srcMaskedWord_eq I hbad)
      have hallowWord :=
        transferFromAllowanceWord_accountMapEquiv (σ := σ_evm) (evm := evmSolm) (I := I)
          hownerSolm hsourceSolm hAccounts
      by_cases hmax :
          (transferFromEvmAllowanceWord σ_evm I).toNat = UInt256.size - 1
      · have hmaxBody : (transferFromAllowanceWord evmSolm I).toNat = UInt256.size - 1 := by
          rw [← hallowWord]
          exact hmax
        by_cases hfit :
            (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                (transferFromWadWord I).toNat < UInt256.size
        · rcases transferFromTailSolmBridge hownerSolm hAccounts hsrcEnough hfit with
            ⟨hsrcEnoughBody, hfitBody, hfinal⟩
          have hbodyTf :
              ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                transferFromTransition.body
                (.returned { contract := contract, locals := transferFromCallStore I }
                  (transferFromPostStateFrom evmSolm I) (some [.bool true])) := by
            simpa [evmSolm] using
              daiTransferFromCallBodyReturns_skipMax evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsrcEnoughBody
                (by simpa [evmSolm, initState] using hsrcIsSender)
                hmaxBody
                hfitBody
          obtain ⟨cs, hbody⟩ := hwrapReturn (by simpa [evmSolm] using hbodyTf)
          obtain ⟨_, _, rdret⟩ :=
            daiTransferFromX_skipMaxSuccessJump
              (I := I) (σ := σ_evm) (ret := ret) (S := S)
              hperm hneWord hmax hsrcEnough hfit hSlen hretDest rd1515
          have hrdret :=
            hfinish
              (transferFromTailDstStoreMem_size I (transferFromAllowanceHashMem_size I))
              (transferFromTailDstStoreMem_read64 I (transferFromAllowanceHashMem_size I)
                (transferFromAllowanceHashMem_read64 I))
              rdret
          exact hrdret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            (by
              simp [transferFromPostStateFrom, transferFromAfterSrcDebitState, evmSolm,
                initState, storageStore_createdAccounts])
            hfinal
            henc
        · have hover :
            UInt256.size ≤
              (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                (transferFromWadWord I).toNat := by omega
          rcases transferFromTailSolmPrefixBridge hownerSolm hAccounts hsrcEnough with
            ⟨hsrcEnoughBody, hcreditNat, _⟩
          have hoverBody :
              UInt256.size ≤
                transferFromDstCreditNat (transferFromAfterSrcDebitState evmSolm I) I := by
            rw [hcreditNat]
            exact hover
          have hbodyTf :
              ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                transferFromTransition.body .reverted := by
            simpa [evmSolm] using
              daiTransferFromCallBodyReverts_dstOverflow_skipMax evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsrcEnoughBody
                (by simpa [evmSolm, initState] using hsrcIsSender)
                hmaxBody
                hoverBody
          exact
            (daiTransferFromX_skipMaxDstOverflowRevertCont
                (I := I) (σ := σ_evm) (ret := ret) (S := S)
                hperm hneWord hmax hsrcEnough hover hSlen rd1515)
            |>.reEquivExecutionRevert hcode hdispatch hdecode
              (hwrapRevert (by simpa [evmSolm] using hbodyTf))
      · by_cases hallowEnough :
            (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ_evm I).toNat
        · have hnotMaxBody :
              (transferFromAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
            rw [← hallowWord]
            exact hmax
          have hallowEnoughBody :
              (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evmSolm I).toNat := by
            rw [← hallowWord]
            exact hallowEnough
          have hallowAcc :=
            transferFromAfterAllowance_accountMapEquiv
              (σ := σ_evm) (evm := evmSolm) (I := I)
              hownerSolm hsourceSolm hAccounts hallowEnough
          let evmAfterAllowance := transferFromAfterAllowanceState evmSolm I
          have hownerAfterAllowance :
              evmAfterAllowance.executionEnv.codeOwner = I.codeOwner := by
            simpa [evmAfterAllowance, transferFromAfterAllowance_codeOwner evmSolm I]
              using hownerSolm
          by_cases hsrcDebitEnough :
              (transferFromWadWord I).toNat ≤
                (transferFromEvmTailSrcBalanceWord
                  (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat
          · by_cases hfit :
              (transferFromEvmTailDstBalanceWord
                  (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat +
                  (transferFromWadWord I).toNat < UInt256.size
            · rcases transferFromTailSolmBridge hownerAfterAllowance hallowAcc
                  hsrcDebitEnough hfit with
                ⟨hsrcDebitEnoughBody, hfitBody, hfinal⟩
              have hbodyTf :
                  ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                    transferFromTransition.body
                    (.returned { contract := contract, locals := transferFromCallStore I }
                      (transferFromPostStateFrom evmAfterAllowance I)
                      (some [.bool true])) := by
                simpa [evmAfterAllowance, evmSolm] using
                  daiTransferFromCallBodyReturns_spend evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    hsrcEnoughSolm
                    (by simpa [evmSolm, initState] using hsrcIsSender)
                    hnotMaxBody
                    hallowEnoughBody
                    hsrcDebitEnoughBody
                    hfitBody
              obtain ⟨cs, hbody⟩ := hwrapReturn (by simpa [evmSolm] using hbodyTf)
              obtain ⟨_, _, rdret⟩ :=
                daiTransferFromX_spendSuccessJump
                  (I := I) (σ := σ_evm) (ret := ret) (S := S)
                  hperm hneWord hmax hallowEnough hsrcDebitEnough hfit hSlen hretDest rd1515
              have hrdret :=
                hfinish
                  (transferFromTailDstStoreMem_size I
                    (transferFromAllowancePostStoreHashMem_size I))
                  (transferFromTailDstStoreMem_read64 I
                    (transferFromAllowancePostStoreHashMem_size I)
                    (transferFromAllowancePostStoreHashMem_read64 I))
                  rdret
              exact hrdret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                (by
                  simp [transferFromPostStateFrom, transferFromAfterSrcDebitState,
                    evmAfterAllowance, transferFromAfterAllowanceState, evmSolm, initState,
                    storageStore_createdAccounts])
                hfinal
                henc
            · have hover :
                UInt256.size ≤
                  (transferFromEvmTailDstBalanceWord
                    (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat +
                    (transferFromWadWord I).toNat := by omega
              rcases transferFromTailSolmPrefixBridge hownerAfterAllowance hallowAcc
                  hsrcDebitEnough with
                ⟨hsrcDebitEnoughBody, hcreditNat, _⟩
              have hoverBody :
                  UInt256.size ≤
                    transferFromDstCreditNat
                      (transferFromAfterSrcDebitState evmAfterAllowance I) I := by
                rw [hcreditNat]
                exact hover
              have hbodyTf :
                  ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                    transferFromTransition.body .reverted := by
                simpa [evmAfterAllowance, evmSolm] using
                  daiTransferFromCallBodyReverts_dstOverflow_spend evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    hsrcEnoughSolm
                    (by simpa [evmSolm, initState] using hsrcIsSender)
                    hnotMaxBody
                    hallowEnoughBody
                    hsrcDebitEnoughBody
                    hoverBody
              exact
                (daiTransferFromX_spendDstOverflowRevertCont
                    (I := I) (σ := σ_evm) (ret := ret) (S := S)
                    hperm hneWord hmax hallowEnough hsrcDebitEnough hover hSlen rd1515)
                |>.reEquivExecutionRevert hcode hdispatch hdecode
                  (hwrapRevert (by simpa [evmSolm] using hbodyTf))
          · have hltDebit :
              (transferFromEvmTailSrcBalanceWord
                  (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat <
                (transferFromWadWord I).toNat := by omega
            have hsrcAfterWord :
                transferFromEvmTailSrcBalanceWord
                    (transferFromEvmAfterAllowanceAccountMap σ_evm I) I =
                  transferFromSrcBalanceWord evmAfterAllowance I := by
              have hread :=
                accountMapEquiv_storage_findD hallowAcc I.codeOwner
                  (transferFromEvmSrcSlot I) (⟨0⟩ : UInt256)
              simpa [evmAfterAllowance, transferFromEvmTailSrcBalanceWord,
                transferFromSrcBalanceWord, transferFromEvmSrcSlot,
                transferFromSrcSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
                State.lookupAccount, Account.lookupStorage, solcSlotWord,
                hownerAfterAllowance] using hread
            have hltDebitBody :
                (transferFromSrcBalanceWord evmAfterAllowance I).toNat <
                  (transferFromWadWord I).toNat := by
              rw [← hsrcAfterWord]
              exact hltDebit
            have hbodyTf :
                ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                  transferFromTransition.body .reverted := by
              simpa [evmAfterAllowance, evmSolm] using
                daiTransferFromCallBodyReverts_srcDebit evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  hsrcEnoughSolm
                  (by simpa [evmSolm, initState] using hsrcIsSender)
                  hnotMaxBody
                  hallowEnoughBody
                  hltDebitBody
            exact
              (daiTransferFromX_spendSrcDebitRevertCont
                  (I := I) (σ := σ_evm) (ret := ret) (S := S)
                  hperm hneWord hmax hallowEnough hltDebit hSlen rd1515)
              |>.reEquivExecutionRevert hcode hdispatch hdecode
                (hwrapRevert (by simpa [evmSolm] using hbodyTf))
        · have hltAllow :
              (transferFromEvmAllowanceWord σ_evm I).toNat <
                (transferFromWadWord I).toNat := by omega
          have hnotMaxBody :
              (transferFromAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
            rw [← hallowWord]
            exact hmax
          have hltAllowBody :
              (transferFromAllowanceWord evmSolm I).toNat <
                (transferFromWadWord I).toNat := by
            rw [← hallowWord]
            exact hltAllow
          have hbodyTf :
              ExecTransitionBody config contract evmSolm (transferFromCallStore I)
                transferFromTransition.body .reverted := by
            simpa [evmSolm] using
              daiTransferFromCallBodyReverts_allowance evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsrcEnoughSolm
                (by simpa [evmSolm, initState] using hsrcIsSender)
                hnotMaxBody
                hltAllowBody
          exact
            (daiTransferFromX_allowanceRevertCont
                (I := I) (σ := σ_evm) (ret := ret) (S := S)
                hneWord hmax hltAllow hSlen rd1515)
            |>.reEquivExecutionRevert hcode hdispatch hdecode
              (hwrapRevert (by simpa [evmSolm] using hbodyTf))
  · have hlt :
        (transferFromEvmTailSrcBalanceWord σ_evm I).toNat < (transferFromWadWord I).toNat := by
      omega
    have hltBody :
        (transferFromSrcBalanceWord evmSolm I).toNat < (transferFromWadWord I).toNat := by
      rw [← hsrcWord]
      exact hlt
    have hbodyTf :
        ExecTransitionBody config contract evmSolm (transferFromCallStore I)
          transferFromTransition.body .reverted := by
      simpa [evmSolm] using
        daiTransferFromCallBodyReverts_initialBalance evmSolm I
          (by simp only [evmSolm, initState]; exact hwv)
          hltBody
    exact
      (daiTransferFromX_initialBalanceRevertCont
          (I := I) (σ := σ_evm) (ret := ret) (S := S)
          hlt hSlen rd1411)
      |>.reEquivExecutionRevert hcode hdispatch hdecode
        (hwrapRevert (by simpa [evmSolm] using hbodyTf))

/-- `transferFrom(address,address,uint256)` body refines its Solm transition. -/
theorem daiTransferFromBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 19))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 19) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some transferFromTransition :=
    daiDispatchTransferFrom hsel
  have hreach := daiReachTransferFromBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode := daiDecode_transferFrom_ok (I := I) hsel hsz100
    obtain ⟨_, _, rd1411⟩ :=
      daiTransferFromX_decoded (g := Sat256.ofUInt256 g) hsel hsz100 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hownerSolm : evmSolm.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm, initState]
    have hsourceSolm : evmSolm.executionEnv.source = I.source := by
      simp [evmSolm, initState]
    have hsrcWord :
        transferFromEvmTailSrcBalanceWord σ_evm I =
          transferFromSrcBalanceWord evmSolm I := by
      rw [transferFromSrcBalanceWord_initState (σ := σ_solm)]
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner
        (transferFromEvmSrcSlot I) (⟨0⟩ : UInt256)
    by_cases hsrcEnough :
        (transferFromWadWord I).toNat ≤ (transferFromEvmTailSrcBalanceWord σ_evm I).toNat
    · obtain ⟨_, _, rd1515⟩ := daiTransferFromX_initialBalanceOk hsrcEnough rd1411
      have hsrcEnoughSolm :
          (transferFromWadWord I).toNat ≤ (transferFromSrcBalanceWord evmSolm I).toNat := by
        rw [← hsrcWord]
        exact hsrcEnough
      by_cases hsrcIsSender :
          AccountAddress.ofNat (transferFromSrcWord I).toNat = I.source
      · have heqWord :=
          transferFromSrcMaskedWord_eq_solcSourceWord_of_address_eq I hsrcIsSender
        by_cases hfit :
            (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                (transferFromWadWord I).toNat < UInt256.size
        · rcases transferFromTailSolmBridge hownerSolm hAccounts hsrcEnough hfit with
            ⟨hsrcEnoughBody, hfitBody, hfinal⟩
          have hbody :
              ExecTransitionBody config contract evmSolm (transferFromStore I)
                transferFromTransition.body
                (.returned { contract := contract, locals := transferFromStore I }
                  (transferFromPostStateFrom evmSolm I) (some [.bool true])) := by
            simpa [evmSolm] using
              daiTransferFromBodyReturns_skipSender evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsrcEnoughBody
                (by simpa [evmSolm, initState] using hsrcIsSender)
                hfitBody
          exact (daiTransferFromX_skipSenderSuccess hperm heqWord hsrcEnough hfit rd1515)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by
                simp [transferFromPostStateFrom, transferFromAfterSrcDebitState, evmSolm,
                  initState, storageStore_createdAccounts])
              hfinal
              (returnEquiv_of_encode
                (by simpa [boolTy] using boolTrueReturnEncoding))
        · have hover :
            UInt256.size ≤
              (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                (transferFromWadWord I).toNat := by omega
          rcases transferFromTailSolmPrefixBridge hownerSolm hAccounts hsrcEnough with
            ⟨hsrcEnoughBody, hcreditNat, _⟩
          have hoverBody :
              UInt256.size ≤
                transferFromDstCreditNat (transferFromAfterSrcDebitState evmSolm I) I := by
            rw [hcreditNat]
            exact hover
          have hbody :
              ExecTransitionBody config contract evmSolm (transferFromStore I)
                transferFromTransition.body .reverted := by
            simpa [evmSolm] using
              daiTransferFromBodyReverts_dstOverflow_skipSender evmSolm I
                (by simp only [evmSolm, initState]; exact hwv)
                hsrcEnoughBody
                (by simpa [evmSolm, initState] using hsrcIsSender)
                hoverBody
          exact (daiTransferFromX_skipSenderDstOverflowRevert hperm heqWord hsrcEnough hover
              rd1515)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hneWord : transferFromSrcMaskedWord I ≠ solcSourceWord I := by
          intro hbad
          exact hsrcIsSender (transferFrom_address_eq_of_srcMaskedWord_eq I hbad)
        have hallowWord :=
          transferFromAllowanceWord_accountMapEquiv (σ := σ_evm) (evm := evmSolm) (I := I)
            hownerSolm hsourceSolm hAccounts
        by_cases hmax :
            (transferFromEvmAllowanceWord σ_evm I).toNat = UInt256.size - 1
        · have hmaxBody : (transferFromAllowanceWord evmSolm I).toNat = UInt256.size - 1 := by
            rw [← hallowWord]
            exact hmax
          by_cases hfit :
              (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                  (transferFromWadWord I).toNat < UInt256.size
          · rcases transferFromTailSolmBridge hownerSolm hAccounts hsrcEnough hfit with
              ⟨hsrcEnoughBody, hfitBody, hfinal⟩
            have hbody :
                ExecTransitionBody config contract evmSolm (transferFromStore I)
                  transferFromTransition.body
                  (.returned { contract := contract, locals := transferFromStore I }
                    (transferFromPostStateFrom evmSolm I) (some [.bool true])) := by
              simpa [evmSolm] using
                daiTransferFromBodyReturns_skipMax evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  hsrcEnoughBody
                  (by simpa [evmSolm, initState] using hsrcIsSender)
                  hmaxBody
                  hfitBody
            exact (daiTransferFromX_skipMaxSuccess hperm hneWord hmax hsrcEnough hfit rd1515)
              |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                (by
                  simp [transferFromPostStateFrom, transferFromAfterSrcDebitState, evmSolm,
                    initState, storageStore_createdAccounts])
                hfinal
                (returnEquiv_of_encode
                  (by simpa [boolTy] using boolTrueReturnEncoding))
          · have hover :
              UInt256.size ≤
                (transferFromEvmTailDstBalanceWord σ_evm I).toNat +
                  (transferFromWadWord I).toNat := by omega
            rcases transferFromTailSolmPrefixBridge hownerSolm hAccounts hsrcEnough with
              ⟨hsrcEnoughBody, hcreditNat, _⟩
            have hoverBody :
                UInt256.size ≤
                  transferFromDstCreditNat (transferFromAfterSrcDebitState evmSolm I) I := by
              rw [hcreditNat]
              exact hover
            have hbody :
                ExecTransitionBody config contract evmSolm (transferFromStore I)
                  transferFromTransition.body .reverted := by
              simpa [evmSolm] using
                daiTransferFromBodyReverts_dstOverflow_skipMax evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  hsrcEnoughBody
                  (by simpa [evmSolm, initState] using hsrcIsSender)
                  hmaxBody
                  hoverBody
            exact (daiTransferFromX_skipMaxDstOverflowRevert hperm hneWord hmax hsrcEnough hover
                rd1515)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · by_cases hallowEnough :
              (transferFromWadWord I).toNat ≤ (transferFromEvmAllowanceWord σ_evm I).toNat
          · have hnotMaxBody :
                (transferFromAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
              rw [← hallowWord]
              exact hmax
            have hallowEnoughBody :
                (transferFromWadWord I).toNat ≤ (transferFromAllowanceWord evmSolm I).toNat := by
              rw [← hallowWord]
              exact hallowEnough
            have hallowAcc :=
              transferFromAfterAllowance_accountMapEquiv
                (σ := σ_evm) (evm := evmSolm) (I := I)
                hownerSolm hsourceSolm hAccounts hallowEnough
            let evmAfterAllowance := transferFromAfterAllowanceState evmSolm I
            have hownerAfterAllowance :
                evmAfterAllowance.executionEnv.codeOwner = I.codeOwner := by
              simpa [evmAfterAllowance, transferFromAfterAllowance_codeOwner evmSolm I]
                using hownerSolm
            by_cases hsrcDebitEnough :
                (transferFromWadWord I).toNat ≤
                  (transferFromEvmTailSrcBalanceWord
                    (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat
            · by_cases hfit :
                (transferFromEvmTailDstBalanceWord
                    (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat +
                    (transferFromWadWord I).toNat < UInt256.size
              · rcases transferFromTailSolmBridge hownerAfterAllowance hallowAcc
                    hsrcDebitEnough hfit with
                  ⟨hsrcDebitEnoughBody, hfitBody, hfinal⟩
                have hbody :
                    ExecTransitionBody config contract evmSolm (transferFromStore I)
                      transferFromTransition.body
                      (.returned { contract := contract, locals := transferFromStore I }
                        (transferFromPostStateFrom evmAfterAllowance I)
                        (some [.bool true])) := by
                  simpa [evmAfterAllowance, evmSolm] using
                    daiTransferFromBodyReturns_spend evmSolm I
                      (by simp only [evmSolm, initState]; exact hwv)
                      hsrcEnoughSolm
                      (by simpa [evmSolm, initState] using hsrcIsSender)
                      hnotMaxBody
                      hallowEnoughBody
                      hsrcDebitEnoughBody
                      hfitBody
                exact (daiTransferFromX_spendSuccess hperm hneWord hmax hallowEnough
                    hsrcDebitEnough hfit rd1515)
                  |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                    (by
                      simp [transferFromPostStateFrom, transferFromAfterSrcDebitState,
                        evmAfterAllowance, transferFromAfterAllowanceState, evmSolm, initState,
                        storageStore_createdAccounts])
                    hfinal
                    (returnEquiv_of_encode
                      (by simpa [boolTy] using boolTrueReturnEncoding))
              · have hover :
                  UInt256.size ≤
                    (transferFromEvmTailDstBalanceWord
                      (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat +
                      (transferFromWadWord I).toNat := by omega
                rcases transferFromTailSolmPrefixBridge hownerAfterAllowance hallowAcc
                    hsrcDebitEnough with
                  ⟨hsrcDebitEnoughBody, hcreditNat, _⟩
                have hoverBody :
                    UInt256.size ≤
                      transferFromDstCreditNat
                        (transferFromAfterSrcDebitState evmAfterAllowance I) I := by
                  rw [hcreditNat]
                  exact hover
                have hbody :
                    ExecTransitionBody config contract evmSolm (transferFromStore I)
                      transferFromTransition.body .reverted := by
                  simpa [evmAfterAllowance, evmSolm] using
                    daiTransferFromBodyReverts_dstOverflow_spend evmSolm I
                      (by simp only [evmSolm, initState]; exact hwv)
                      hsrcEnoughSolm
                      (by simpa [evmSolm, initState] using hsrcIsSender)
                      hnotMaxBody
                      hallowEnoughBody
                      hsrcDebitEnoughBody
                      hoverBody
                exact (daiTransferFromX_spendDstOverflowRevert hperm hneWord hmax hallowEnough
                    hsrcDebitEnough hover rd1515)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hltDebit :
                (transferFromEvmTailSrcBalanceWord
                    (transferFromEvmAfterAllowanceAccountMap σ_evm I) I).toNat <
                  (transferFromWadWord I).toNat := by omega
              have hsrcAfterWord :
                  transferFromEvmTailSrcBalanceWord
                      (transferFromEvmAfterAllowanceAccountMap σ_evm I) I =
                    transferFromSrcBalanceWord evmAfterAllowance I := by
                have hread :=
                  accountMapEquiv_storage_findD hallowAcc I.codeOwner
                    (transferFromEvmSrcSlot I) (⟨0⟩ : UInt256)
                simpa [evmAfterAllowance, transferFromEvmTailSrcBalanceWord,
                  transferFromSrcBalanceWord, transferFromEvmSrcSlot,
                  transferFromSrcSlot_eq_mapSlot_masked, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, solcSlotWord,
                  hownerAfterAllowance] using hread
              have hltDebitBody :
                  (transferFromSrcBalanceWord evmAfterAllowance I).toNat <
                    (transferFromWadWord I).toNat := by
                rw [← hsrcAfterWord]
                exact hltDebit
              have hbody :
                  ExecTransitionBody config contract evmSolm (transferFromStore I)
                    transferFromTransition.body .reverted := by
                simpa [evmAfterAllowance, evmSolm] using
                  daiTransferFromBodyReverts_srcDebit evmSolm I
                    (by simp only [evmSolm, initState]; exact hwv)
                    hsrcEnoughSolm
                    (by simpa [evmSolm, initState] using hsrcIsSender)
                    hnotMaxBody
                    hallowEnoughBody
                    hltDebitBody
              exact (daiTransferFromX_spendSrcDebitRevert hperm hneWord hmax hallowEnough
                  hltDebit rd1515)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hltAllow :
                (transferFromEvmAllowanceWord σ_evm I).toNat <
                  (transferFromWadWord I).toNat := by omega
            have hnotMaxBody :
                (transferFromAllowanceWord evmSolm I).toNat ≠ UInt256.size - 1 := by
              rw [← hallowWord]
              exact hmax
            have hltAllowBody :
                (transferFromAllowanceWord evmSolm I).toNat <
                  (transferFromWadWord I).toNat := by
              rw [← hallowWord]
              exact hltAllow
            have hbody :
                ExecTransitionBody config contract evmSolm (transferFromStore I)
                  transferFromTransition.body .reverted := by
              simpa [evmSolm] using
                daiTransferFromBodyReverts_allowance evmSolm I
                  (by simp only [evmSolm, initState]; exact hwv)
                  hsrcEnoughSolm
                  (by simpa [evmSolm, initState] using hsrcIsSender)
                  hnotMaxBody
                  hltAllowBody
            exact (daiTransferFromX_allowanceRevert hneWord hmax hltAllow rd1515)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hlt :
          (transferFromEvmTailSrcBalanceWord σ_evm I).toNat < (transferFromWadWord I).toNat := by
        omega
      have hltBody :
          (transferFromSrcBalanceWord evmSolm I).toNat < (transferFromWadWord I).toNat := by
        rw [← hsrcWord]
        exact hlt
      have hbody :
          ExecTransitionBody config contract evmSolm (transferFromStore I)
            transferFromTransition.body .reverted := by
        simpa [evmSolm] using
          daiTransferFromBodyReverts_initialBalance evmSolm I
            (by simp only [evmSolm, initState]; exact hwv)
            hltBody
      exact (daiTransferFromX_initialBalanceRevert hlt rd1411)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact daiTransferFromBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
