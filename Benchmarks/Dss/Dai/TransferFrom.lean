import Benchmarks.Dss.Dai.Dispatch
import Benchmarks.Dss.Dai.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Dai

/-! ## ABI decode and external wrapper for `transferFrom(address,address,uint256)` -/

abbrev transferFromSrcWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev transferFromSrcMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromSrcWord I)

abbrev transferFromDstWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev transferFromDstMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferFromDstWord I)

abbrev transferFromWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev transferFromSrcValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromSrcWord I).toNat)

abbrev transferFromDstValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferFromDstWord I).toNat)

abbrev transferFromWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferFromWadWord I).toNat)

abbrev transferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "src" (transferFromSrcValue I)).insert "dst"
    (transferFromDstValue I)).insert "wad" (transferFromWadValue I)

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

theorem daiDecode_transferFrom_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (transferFromStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["src", "dst", "wad"] [addr, addr, uint256]
    I.calldata = _
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
    simpa [transferFromWadWord, transferFromDstMaskedWord, transferFromSrcMaskedWord,
      transferFromSrcWord, transferFromDstWord, calldataWord] using rd1411⟩

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

def transferFromSrcBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromSrcSlot I)

def transferFromDstBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromDstSlot I)

def transferFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferFromAllowanceSlot evm I)

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
    (her := by
      simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromSrcBalanceRef,
        transferFromSrcValue, transferFromSrcKey, valueToKey?, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?, transferFromStore_index_src])
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
    (her := by
      simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferFromDstBalanceRef,
        transferFromDstValue, transferFromDstKey, valueToKey?, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?, transferFromStore_index_dst])
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
    (her := by
      simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue,
        transferFromAllowanceRef, transferFromSrcValue, transferFromSrcKey,
        transferFromSpenderKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, evalExpr?, transferFromStore_index_src])
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

theorem transferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I } evm
      .storage (allowanceRef (.var "src") sender)
      (.int (Int.ofNat (transferFromAllowanceDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromAfterAllowanceState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (transferFromAllowanceSlot evm I) (.int uint256Int))
      (hbase := transferFromStore_allowance I)
      (her := by
        simp [evalStorageRef, evalStorageRefStep, sender, envValue, transferFromAllowanceRef,
          transferFromSrcValue, transferFromSrcKey, transferFromSpenderKey, valueToKey?,
          EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, transferFromStore_index_src])
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          transferFromSpenderKey, uint256St])
      (hloc := by rfl)
  simpa [transferFromAfterAllowanceState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (transferFromAllowanceSlot evm I)
      (transferFromAllowanceDebitWord evm I)

theorem transferFromAssignSrc (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I } evm
      .storage (balanceOfRef (.var "src"))
      (.int (Int.ofNat (transferFromSrcDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromAfterSrcDebitState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (transferFromSrcSlot I) (.int uint256Int))
      (hbase := transferFromStore_balanceOf I)
      (her := by
        simp [evalStorageRef, evalStorageRefStep, transferFromSrcBalanceRef,
          transferFromSrcValue, transferFromSrcKey, valueToKey?, EvalResult.bind,
          EvalResult.ofOption, bind, pure, evalExpr?, transferFromStore_index_src])
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromSrcKey,
          uint256St])
      (hloc := by rfl)
  simpa [transferFromAfterSrcDebitState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (transferFromSrcSlot I) (transferFromSrcDebitWord evm I)

theorem transferFromAssignDst (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferFromDstCreditNat (transferFromAfterSrcDebitState evm I) I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferFromStore I }
      (transferFromAfterSrcDebitState evm I) .storage (balanceOfRef (.var "dst"))
      (transferFromDstCreditValue (transferFromAfterSrcDebitState evm I) I) =
        .ok ({ contract := contract, locals := transferFromStore I },
          transferFromPostStateFrom evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (transferFromDstSlot I) (.int uint256Int))
      (hbase := transferFromStore_balanceOf I)
      (her := by
        simp [evalStorageRef, evalStorageRefStep, transferFromDstBalanceRef,
          transferFromDstValue, transferFromDstKey, valueToKey?, EvalResult.bind,
          EvalResult.ofOption, bind, pure, evalExpr?, transferFromStore_index_dst])
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, transferFromDstKey,
          uint256St])
      (hloc := by rfl)
  rw [← transferFromDstCreditWord_toNat (transferFromAfterSrcDebitState evm I) I hfit]
  simpa [transferFromPostStateFrom, wordLoc, uint256Loc, uint256Int,
    transferFromAfterSrcDebit_codeOwner] using
    storageLocStore_uint256 (transferFromAfterSrcDebitState evm I) (transferFromDstSlot I)
      (transferFromDstCreditWord (transferFromAfterSrcDebitState evm I) I)

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

/-- `transferFrom(address,address,uint256)` body refines its Solm transition. -/
theorem daiTransferFromBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiSelBytes 19))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiSelBytes 19) (by native_decide) hsel
  have hdispatch : dispatchMsg contract I.calldata = some transferFromTransition :=
    daiDispatchTransferFrom hsel
  have hreach := daiReachTransferFromBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · sorry
  · exact daiTransferFromBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dai
