import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.TransferRoutines
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

/-! ## `transfer(address,uint256)` source slice and EVM entry prefix -/

/-- The raw ABI word for `transfer`'s `to` argument. -/
abbrev transferToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev transferToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (transferToWord I)

/-- The raw ABI word for `transfer`'s `value` argument. -/
abbrev transferValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev transferToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferToWord I).toNat)

abbrev transferValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferValueWord I).toNat)

abbrev transferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "to" (transferToValue I)).insert "value" (transferValueValue I)

abbrev transferToKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (transferToWord I).toNat)

def transferSenderSlot (evm : EVM.State) : UInt256 :=
  balanceOfSlot (.address evm.executionEnv.source)

def transferToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (transferToKey I)

theorem transferToSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    transferToSlot I = mapSlot (transferToMaskedWord I) ⟨1⟩ := by
  unfold transferToSlot balanceOfSlot transferToKey transferToMaskedWord
  rw [keyValueToWord_address_ofNat_mask]

def transferFromBalanceWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (transferSenderSlot evm)

abbrev transferFromBalanceValue (evm : EVM.State) : Value :=
  .int (Int.ofNat (transferFromBalanceWord evm).toNat)

abbrev transferStoreFromBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStore I).insert "fromBalance" (transferFromBalanceValue evm)

def transferDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((transferFromBalanceWord evm).toNat - (transferValueWord I).toNat)

def transferAfterDebitState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (transferSenderSlot evm)
    (transferDebitWord evm I)

theorem transferAfterDebit_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (transferAfterDebitState evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  simp only [transferAfterDebitState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

def transferToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (transferAfterDebitState evm I) evm.executionEnv.codeOwner
    (transferToSlot I)

abbrev transferToBalanceValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferToBalanceWord evm I).toNat)

abbrev transferStoreToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStoreFromBalance evm I).insert "toBalance" (transferToBalanceValue evm I)

def transferNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (transferToBalanceWord evm I).toNat + (transferValueWord I).toNat

def transferNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (transferNewToNat evm I)

abbrev transferNewToValue (evm : EVM.State) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferNewToNat evm I))

def transferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferAfterDebitState evm I) evm.executionEnv.codeOwner
    (transferToSlot I) (transferNewToWord evm I)

theorem transferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    (transferNewToWord evm I).toNat = transferNewToNat evm I := by
  unfold transferNewToWord
  exact ulit_toNat' _ hfit

theorem uniswapDecode_transfer_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to", "value"] [legacyAddr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferToValue, transferValueValue,
    transferToWord, transferValueWord, calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "to") (y := "value") hsz68

theorem uniswapDecode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["to", "value"] [legacyAddr, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_legacyAddress_uint256_none_short
      (cd := I.calldata) (x := "to") (y := "value") hsz4 hshort

theorem uniswapDecode_transfer_ok_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (_hnc : ¬ (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to", "value"] [legacyAddr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferToValue, transferValueValue,
    transferToWord, transferValueWord, calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "to") (y := "value") hsz68

theorem transferStore_to (I : ExecutionEnv) :
    (transferStore I).get? "to" = some (transferToValue I) := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_self]

theorem transferStore_value (I : ExecutionEnv) :
    (transferStore I).get? "value" = some (transferValueValue I) := by
  rw [transferStore, store_get_self]

theorem transferStore_balanceOf (I : ExecutionEnv) :
    (transferStore I).get? "balanceOf" = none := by
  rw [transferStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem transferStoreFromBalance_fromBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "fromBalance" =
      some (transferFromBalanceValue evm) := by
  rw [transferStoreFromBalance, store_get_self]

theorem transferStoreFromBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "value" = some (transferValueValue I) := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_value]

theorem transferStoreFromBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "to" = some (transferToValue I) := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_to]

theorem transferStoreFromBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I).get? "balanceOf" = none := by
  rw [transferStoreFromBalance, store_get_ne _ _ (by decide), transferStore_balanceOf]

theorem transferStoreToBalance_toBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreToBalance evm I).get? "toBalance" =
      some (transferToBalanceValue evm I) := by
  rw [transferStoreToBalance, store_get_self]

theorem transferStoreToBalance_value (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreToBalance evm I).get? "value" = some (transferValueValue I) := by
  rw [transferStoreToBalance, store_get_ne _ _ (by decide), transferStoreFromBalance_value]

theorem transferStoreToBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreToBalance evm I).get? "to" = some (transferToValue I) := by
  rw [transferStoreToBalance, store_get_ne _ _ (by decide), transferStoreFromBalance_to]

theorem evalExpr_transfer_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_to]

theorem evalExpr_transfer_to_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_to]

theorem evalExpr_transfer_to_toBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStoreToBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreToBalance_to]

theorem evalExpr_transfer_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.var "value") = .ok (transferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_value]

def transferSenderEvaledRef (evm : EVM.State) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStore I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, sender, envValue,
    transferSenderEvaledRef, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalStorageRef_transfer_sender_balance_fromBalance
    (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStoreFromBalance evm I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, sender, envValue,
    transferSenderEvaledRef, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStore I } evm
      (.storage (balanceOfRef sender)) = .ok (transferFromBalanceValue evm) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [transferStore, balanceOfRef])
    (her := evalStorageRef_transfer_sender_balance evm I)
    (hty := by simp [storageTypeAt?, transferSenderEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferSenderSlot, transferFromBalanceWord, uniswapStorageLocLoad_uint256]

def transferToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (transferToKey I)] }

theorem evalStorageRef_transfer_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStoreFromBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferToEvaledRef,
    transferToValue, transferToKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
    pure, evalExpr_transfer_to_fromBalance]

theorem evalStorageRef_transfer_to_balance_toBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := transferStoreToBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferToEvaledRef,
    transferToValue, transferToKey, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind,
    pure, evalExpr_transfer_to_toBalance]

theorem evalExpr_transfer_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? config { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_transfer_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?]
  omega

theorem evalExpr_transfer_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? config { contract := contract, locals := transferStoreFromBalance evm I } evm
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (.int (Int.ofNat (transferDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromBalanceWord evm).toNat -
          Int.ofNat (transferValueWord I).toNat =
        Int.ofNat ((transferFromBalanceWord evm).toNat - (transferValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (transferDebitWord evm I).toNat =
        (transferFromBalanceWord evm).toNat - (transferValueWord I).toNat := by
    unfold transferDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, htoNat]
  exact hsub

theorem transferAssignSender (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := transferStoreFromBalance evm I } evm
      .storage (balanceOfRef sender) (.int (Int.ofNat (transferDebitWord evm I).toNat)) =
        .ok ({ contract := contract, locals := transferStoreFromBalance evm I },
          transferAfterDebitState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [transferStoreFromBalance, balanceOfRef])
      (her := evalStorageRef_transfer_sender_balance_fromBalance evm I)
      (hty := by simp [storageTypeAt?, transferSenderEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [transferAfterDebitState, transferSenderSlot]

theorem evalExpr_transfer_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := transferStoreFromBalance evm I }
      (transferAfterDebitState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferToBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [transferStoreFromBalance, balanceOfRef])
    (her := evalStorageRef_transfer_to_balance_fromBalance evm (transferAfterDebitState evm I) I)
    (hty := by simp [storageTypeAt?, transferToEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [transferToSlot, transferToBalanceWord, uniswapStorageLocLoad_uint256,
    transferAfterDebit_codeOwner]

theorem evalExpr_transfer_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I) (u256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, transferNewToValue, transferNewToNat, uint256Int]
  constructor
  · omega
  · have hfitNat :
        (transferToBalanceWord evm I).toNat + (transferValueWord I).toNat < 2 ^ 256 := by
      simpa [transferNewToNat, UInt256.size] using hfit
    omega

theorem evalExpr_transfer_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    evalExpr? config { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (u256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, uint256Int]
  intro _
  simpa [transferNewToNat] using hge

theorem transferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I) .storage (balanceOfRef (.var "to"))
      (transferNewToValue evm I) =
        .ok ({ contract := contract, locals := transferStoreToBalance evm I },
          transferPostState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [transferStoreToBalance, transferStoreFromBalance, balanceOfRef])
      (her := evalStorageRef_transfer_to_balance_toBalance evm (transferAfterDebitState evm I) I)
      (hty := by simp [storageTypeAt?, transferToEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [← transferNewToWord_toNat evm I hfit]
  rw [uniswapStorageLocStore_uint256]
  simp [transferPostState, transferToSlot, transferAfterDebit_codeOwner]

theorem uniswapTransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (transferStore I) transferTransition.body
      (.returned { contract := contract, locals := transferStoreToBalance evm I }
        (transferPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_newToBalance evm I hfit)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem uniswapTransferBodyReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    ExecTransitionBody config contract evm (transferStore I) transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem uniswapTransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecTransitionBody config contract evm (transferStore I) transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.assignExprRevert (evalExpr_transfer_newToBalance_revert evm I hover))

/-- The optimized external wrapper for `transfer(address,uint256)` masks address calldata and
    jumps to the external transfer routine at pc 5061. -/
theorem uniswapTransferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5061⟩
      [transferValueWord I, transferToMaskedWord I, ⟨797⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1256⟩ := RD.uniswapAddressUint256ExternalLenOk
    (entry := ⟨1234⟩) (ret := ⟨797⟩) (routine := ⟨5061⟩) hreach
    uniswap_address_uint256_external_entry_wf (by jump_dest) hsz68 hsize
  obtain ⟨_, _, rd5061⟩ := RD.uniswapAddressUint256ExternalMaskAndJumpMasked
    (entry := ⟨1234⟩) (ret := ⟨797⟩) (routine := ⟨5061⟩) (R := [sel]) rd1256
    uniswap_address_uint256_external_entry_wf
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by simpa [transferToWord, transferToMaskedWord, transferValueWord] using rd5061⟩

/-- Short-calldata path for `transfer(address,uint256)` from the dispatcher body entry.

This covers calldata with a selector present but fewer than two ABI words. The dispatcher-level
`calldatasize < 4` branch remains in `Correct.lean`.
-/
theorem uniswapTransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.uniswapAddressUint256ExternalShort
    (entry := ⟨1234⟩) (ret := ⟨797⟩) (routine := ⟨5061⟩)
    hreach uniswap_address_uint256_external_entry_wf hsz4 hsize hshort

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc external routine that injects `CALLER`
-- as the source address and jumps to a shared private transfer routine with a dynamic continuation.
theorem RD.uniswapTransferExternalToInternal {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value toWord ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD uniswapV2PairBytecode ee g s0 ⟨5061⟩ (value :: toWord :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode ee g s0 ⟨7510⟩
      (value :: toWord :: uniswapSourceWord ee :: ⟨2907⟩ :: ⟨0⟩ :: value :: toWord :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd7510₀ := evm_run h with [
    jumpdest, push1 ⟨0⟩, push2 ⟨2907⟩, caller, dup5, dup5, push2 ⟨7510⟩]
  exact ⟨_, _, by
    simpa [uniswapSourceWord] using rd7510₀.jump (by decide) (by jump_dest) (by evm_ov)⟩

/-- Chained success prefix for `transfer(address,uint256)`, from the dispatcher body pc
    to the shared internal `_transfer` routine at pc 7510. -/
theorem uniswapTransferX_toInternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7510⟩
      (transferValueWord I :: transferToMaskedWord I :: uniswapSourceWord I :: ⟨2907⟩ ::
        ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5061⟩ := uniswapTransferX_decoded (g := g)
    hsz68 hsize hreach
  obtain ⟨_, _, rd7510⟩ := RD.uniswapTransferExternalToInternal
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (ret := ⟨797⟩)
    (R := [sel]) rd5061 (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, rd7510⟩

/-- Chained success prefix for `transfer(address,uint256)`, from the dispatcher body pc
    through the sender-balance checked subtraction in the shared `_transfer` routine. -/
theorem uniswapTransferX_afterDebit {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7551⟩
      (transferDebitWord (initState cA gh bl σ σ₀ g A I) I :: transferValueWord I ::
        transferToMaskedWord I :: uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ ::
        transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
      (twoWordHashMem (uniswapSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferX_toInternal (g := g)
    hsz68 hsize hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩) =
        transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) := by
    simp [uniswapCodeOwnerStorageWord, transferFromBalanceWord, transferSenderSlot,
      balanceOfSlot, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, keyValueToWord_address, uniswapSourceWord]
  have hbalance :
      (transferValueWord I).toNat ≤
        (uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩)).toNat := by
    rw [hbalanceWord]
    exact henough
  obtain ⟨_, _, rd7551₀⟩ := RD.uniswapTransferInternalAfterDebit
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7510 (uniswapSourceWord_canonical I) hbalance
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub (uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩))
          (transferValueWord I) =
        transferDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    rw [hbalanceWord]
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat
        (transferValueWord I).toNat)
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).val.isLt)]
  have rd7551 := rd7551₀
  rw [hdebit] at rd7551
  exact ⟨_, _, rd7551⟩

/-- Revert path for `transfer(address,uint256)` when the sender balance is smaller than
    `value`, through the checked subtraction in the shared `_transfer` routine. -/
theorem uniswapTransferX_insufficient {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlt : (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat <
      (transferValueWord I).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7510⟩ := uniswapTransferX_toInternal (g := g)
    hsz68 hsize hreach
  have hbalanceWord :
      uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩) =
        transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) := by
    simp [uniswapCodeOwnerStorageWord, transferFromBalanceWord, transferSenderSlot,
      balanceOfSlot, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, keyValueToWord_address, uniswapSourceWord]
  have hltWord :
      (uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩)).toNat <
        (transferValueWord I).toNat := by
    rw [hbalanceWord]
    exact hlt
  obtain ⟨_, _, rd6879⟩ := RD.uniswapTransferInternalFromBalanceLoad
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7510 (uniswapSourceWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.uniswapSafeMathSubUnderflow
    (a := uniswapCodeOwnerStorageWord I σ (mapSlot (uniswapSourceWord I) ⟨1⟩))
    (b := transferValueWord I) (ret := ⟨7551⟩)
    (R := transferValueWord I :: transferToMaskedWord I :: uniswapSourceWord I ::
      ⟨2907⟩ :: ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd6879 hltWord
    (twoWordHashMem_size_96 (uniswapSourceWord I) ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (uniswapSourceWord I) ⟨1⟩ solcFreePtrMem_size
      solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Chained success prefix for `transfer(address,uint256)`, through the sender-balance
    `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferX_afterSenderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: transferValueWord I :: transferToMaskedWord I ::
        uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ :: transferValueWord I ::
        transferToMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferDebitHashMem (uniswapSourceWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7551⟩ := uniswapTransferX_afterDebit (g := g)
    hsz68 hsize henough hreach
  obtain ⟨_, _, rd7582⟩ := RD.uniswapTransferInternalStoreDebit
    (debit := transferDebitWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7551 hperm (uniswapSourceWord_canonical I)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7582⟩

/-- Chained success prefix for `transfer(address,uint256)`, through the recipient-balance
    checked addition in the shared `_transfer` routine. -/
theorem uniswapTransferX_afterCreditCalc {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7604⟩
      (transferNewToWord (initState cA gh bl σ σ₀ g A I) I :: transferValueWord I ::
        transferToMaskedWord I :: uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ ::
        transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferToHashMem (uniswapSourceWord I) (transferToMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferX_afterSenderStore (g := g)
    hsz68 hsize hperm henough hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
    (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩) =
        transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    have htoSlot := transferToSlot_eq_mapSlot_masked I
    simp [σDebit, uniswapCodeOwnerStorageWord, transferToBalanceWord, transferAfterDebitState,
      transferSenderSlot, balanceOfSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, keyValueToWord_address,
      uniswapSourceWord, htoSlot]
  have hfitWord :
      (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩)).toNat +
        (transferValueWord I).toNat < UInt256.size := by
    rw [htoBalanceWord]
    simpa [transferNewToNat] using hfit
  have hcanonToMasked : (transferToMaskedWord I).toNat < EVM.addressModulus := by
    simpa [transferToMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (transferToWord I)
  obtain ⟨_, _, rd7604₀⟩ := RD.uniswapTransferInternalAfterCreditCalc
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7582 hcanonToMasked hfitWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩) +
          transferValueWord I =
        transferNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitWord, htoBalanceWord,
      transferNewToWord_toNat _ _ hfit]
    rfl
  have rd7604 := rd7604₀
  rw [hnew] at rd7604
  exact ⟨_, _, rd7604⟩

/-- Revert path for `transfer(address,uint256)` when crediting the recipient balance overflows
    the checked addition in the shared `_transfer` routine. -/
theorem uniswapTransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hover : UInt256.size ≤
      transferNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd7582⟩ := uniswapTransferX_afterSenderStore (g := g)
    hsz68 hsize hperm henough hreach
  let σDebit := sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
    (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)
  have htoBalanceWord :
      uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩) =
        transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
    have htoSlot := transferToSlot_eq_mapSlot_masked I
    simp [σDebit, uniswapCodeOwnerStorageWord, transferToBalanceWord, transferAfterDebitState,
      transferSenderSlot, balanceOfSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, storageStore_accountMap, keyValueToWord_address,
      uniswapSourceWord, htoSlot]
  have hoverWord :
      UInt256.size ≤
        (uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩)).toNat +
          (transferValueWord I).toNat := by
    rw [htoBalanceWord]
    simpa [transferNewToNat] using hover
  have hcanonToMasked : (transferToMaskedWord I).toNat < EVM.addressModulus := by
    simpa [transferToMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (transferToWord I)
  obtain ⟨_, _, rd8515⟩ := RD.uniswapTransferInternalToBalanceLoad
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7582 hcanonToMasked
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.uniswapSafeMathAddOverflow
    (a := uniswapCodeOwnerStorageWord I σDebit (mapSlot (transferToMaskedWord I) ⟨1⟩))
    (b := transferValueWord I) (ret := ⟨7604⟩)
    (R := transferValueWord I :: transferToMaskedWord I :: uniswapSourceWord I ::
      ⟨2907⟩ :: ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd8515 hoverWord
    (uniswapTransferToHashMem_size (uniswapSourceWord I) (transferToMaskedWord I))
    (uniswapTransferToHashMem_read64 (uniswapSourceWord I) (transferToMaskedWord I))
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Chained success prefix for `transfer(address,uint256)`, through the recipient-balance
    `SSTORE` in the shared `_transfer` routine. -/
theorem uniswapTransferX_afterCreditStore {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD uniswapV2PairBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7638⟩
      (⟨64⟩ :: transferToMaskedWord I :: solcAddrMask :: ⟨32⟩ :: transferValueWord I ::
        transferToMaskedWord I :: uniswapSourceWord I :: ⟨2907⟩ :: ⟨0⟩ ::
        transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
      (uniswapTransferCreditHashMem (uniswapSourceWord I) (transferToMaskedWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferToMaskedWord I) ⟨1⟩)
        (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨_, _, rd7604⟩ := uniswapTransferX_afterCreditCalc (g := g)
    hsz68 hsize hperm henough hfit hreach
  have hcanonToMasked : (transferToMaskedWord I).toNat < EVM.addressModulus := by
    simpa [transferToMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (transferToWord I)
  obtain ⟨_, _, rd7638⟩ := RD.uniswapTransferInternalStoreCredit
    (newTo := transferNewToWord (initState cA gh bl σ σ₀ g A I) I)
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7604 hperm hcanonToMasked
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rd7638⟩

/-- Successful EVM path for `transfer(address,uint256)`, including the shared `_transfer` event
    emission and boolean return wrapper. -/
theorem uniswapX_transfer {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (mapSlot (uniswapSourceWord I) ⟨1⟩)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (mapSlot (transferToMaskedWord I) ⟨1⟩)
        (transferNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd7638⟩ := uniswapTransferX_afterCreditStore (g := g)
    hsz68 hsize hperm henough hfit hreach
  obtain ⟨_, _, rd2907⟩ := RD.uniswapTransferInternalEmitAndJump
    (value := transferValueWord I) (toWord := transferToMaskedWord I) (src := uniswapSourceWord I)
    (ret := ⟨2907⟩)
    (R := ⟨0⟩ :: transferValueWord I :: transferToMaskedWord I :: ⟨797⟩ :: [sel])
    rd7638 hperm (uniswapSourceWord_canonical I) (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd797⟩ := RD.uniswapInternalTransferReturnTrue
    (discard := ⟨0⟩) (a := transferValueWord I) (b := transferToMaskedWord I) (ret := ⟨797⟩)
    (R := [sel]) rd2907 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have htrue : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by decide
  have hstore :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
          (uniswapTransferLogMem (uniswapSourceWord I) (transferToMaskedWord I)
            (transferValueWord I))
          128 32 =
        uniswapTransferReturnMem (uniswapSourceWord I) (transferToMaskedWord I)
          (transferValueWord I) ⟨1⟩ := by
    rw [htrue]
    rfl
  have hread :
      (uniswapTransferReturnMem (uniswapSourceWord I) (transferToMaskedWord I)
          (transferValueWord I) ⟨1⟩).readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    rw [htrue]
    exact uniswapTransferReturnMem_read128 (uniswapSourceWord I) (transferToMaskedWord I)
      (transferValueWord I) ⟨1⟩
  simpa [htrue] using RD.uniswapReturnBool797FromMem
    (val := (⟨1⟩ : UInt256)) (R := [sel])
    (mem := uniswapTransferLogMem (uniswapSourceWord I) (transferToMaskedWord I)
      (transferValueWord I))
    (memout := uniswapTransferReturnMem (uniswapSourceWord I) (transferToMaskedWord I)
      (transferValueWord I) ⟨1⟩)
    rd797
    (uniswapTransferLogMem_mload64 (uniswapSourceWord I) (transferToMaskedWord I)
      (transferValueWord I))
    hstore
    (uniswapTransferReturnMem_mload64 (uniswapSourceWord I) (transferToMaskedWord I)
      (transferValueWord I) ⟨1⟩)
    hread
    (by simp only [List.length_singleton]; omega)

/- Success refinement slice for `transfer(address,uint256)`.

Malformed calldata remains as separate decode-failure work, matching the incremental style used by
the surrounding scaffold.
-/
set_option maxHeartbeats 2000000 in
theorem uniswapTransferBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat)
    (hfit :
      transferNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
        UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
        (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hFromBalance : transferFromBalanceWord evmE = transferFromBalanceWord evmS := by
    unfold transferFromBalanceWord transferSenderSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (balanceOfSlot (.address evmS.executionEnv.source))
  have hDebit : transferDebitWord evmE I = transferDebitWord evmS I := by
    simp [transferDebitWord, hFromBalance]
  have hσDebit : EVMStateEquiv (transferAfterDebitState evmE I)
      (transferAfterDebitState evmS I) := by
    unfold transferAfterDebitState transferSenderSlot
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner (balanceOfSlot (.address evmS.executionEnv.source)) rfl
  have hToBalance : transferToBalanceWord evmE I = transferToBalanceWord evmS I := by
    unfold transferToBalanceWord
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I)
  have hNewToNat : transferNewToNat evmE I = transferNewToNat evmS I := by
    simp [transferNewToNat, hToBalance]
  have hNewToWord : transferNewToWord evmE I = transferNewToWord evmS I := by
    simp [transferNewToWord, hNewToNat]
  have hσPost : EVMStateEquiv (transferPostState evmE I) (transferPostState evmS I) := by
    unfold transferPostState
    rw [hσ.executionEnv, hNewToWord]
    exact hσDebit.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I) rfl
  have henoughS :
      (transferValueWord I).toNat ≤ (transferFromBalanceWord evmS).toNat := by
    simpa [evmE, hFromBalance] using henough
  have hfitS : transferNewToNat evmS I < UInt256.size := by
    simpa [evmE, hNewToNat] using hfit
  have hbody :
      ExecTransitionBody config contract evmS (transferStore I) transferTransition.body
        (.returned { contract := contract, locals := transferStoreToBalance evmS I }
          (transferPostState evmS I) (some (.bool true))) := by
    exact uniswapTransferBodyReturns evmS I (by simp only [evmS, initState]; exact hwv)
      henoughS hfitS
  have htoSlot : transferToSlot I = mapSlot (transferToMaskedWord I) ⟨1⟩ :=
    transferToSlot_eq_mapSlot_masked I
  have hsenderSlot : transferSenderSlot evmE = mapSlot (uniswapSourceWord I) ⟨1⟩ := by
    simp [transferSenderSlot, balanceOfSlot, evmE, initState, keyValueToWord_address,
      uniswapSourceWord]
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (mapSlot (uniswapSourceWord I) ⟨1⟩)
            (transferDebitWord evmE I))
          (mapSlot (transferToMaskedWord I) ⟨1⟩) (transferNewToWord evmE I)).1 =
        (transferPostState evmE I).createdAccounts := by
    simp [transferPostState, transferAfterDebitState, evmE, initState,
      storageStore_createdAccounts]
  have hAccountsPost :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm (mapSlot (uniswapSourceWord I) ⟨1⟩)
            (transferDebitWord evmE I))
          (mapSlot (transferToMaskedWord I) ⟨1⟩) (transferNewToWord evmE I))
        (transferPostState evmE I).accountMap := by
    apply accountMapEquiv.of_eq
    simp only [transferPostState, storageStore_accountMap]
    simp only [transferAfterDebitState, storageStore_accountMap]
    rw [hsenderSlot, htoSlot]
    simp only [evmE, initState]
  exact (uniswapX_transfer (g := Sat256.ofUInt256 g)
      hsz68 hsize hperm henough hfit hreach)
    |>.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
      hcreated hAccountsPost hσPost (returnEquiv_of_encode boolTrueReturnEncoding)

/-- Insufficient-balance revert refinement slice for `transfer(address,uint256)`. -/
theorem uniswapTransferBodyCoreRevert_insufficient
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlt : (transferFromBalanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat <
        (transferValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
        (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hFromBalance : transferFromBalanceWord evmE = transferFromBalanceWord evmS := by
    unfold transferFromBalanceWord transferSenderSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (balanceOfSlot (.address evmS.executionEnv.source))
  have hltS : (transferFromBalanceWord evmS).toNat < (transferValueWord I).toNat := by
    simpa [evmE, hFromBalance] using hlt
  have hbody :
      ExecTransitionBody config contract evmS (transferStore I) transferTransition.body
        .reverted := by
    exact uniswapTransferBodyReverts_insufficient evmS I
      (by simp only [evmS, initState]; exact hwv) hltS
  exact (uniswapTransferX_insufficient (g := Sat256.ofUInt256 g)
      hsz68 hsize hlt hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Checked-add overflow revert refinement slice for `transfer(address,uint256)`. -/
theorem uniswapTransferBodyCoreRevert_overflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat)
    (hover : UInt256.size ≤
      transferNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transferTransition.params.map Param.name)
        (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hFromBalance : transferFromBalanceWord evmE = transferFromBalanceWord evmS := by
    unfold transferFromBalanceWord transferSenderSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (balanceOfSlot (.address evmS.executionEnv.source))
  have hDebit : transferDebitWord evmE I = transferDebitWord evmS I := by
    simp [transferDebitWord, hFromBalance]
  have hσDebit : EVMStateEquiv (transferAfterDebitState evmE I)
      (transferAfterDebitState evmS I) := by
    unfold transferAfterDebitState transferSenderSlot
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner (balanceOfSlot (.address evmS.executionEnv.source)) rfl
  have hToBalance : transferToBalanceWord evmE I = transferToBalanceWord evmS I := by
    unfold transferToBalanceWord
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I)
  have hNewToNat : transferNewToNat evmE I = transferNewToNat evmS I := by
    simp [transferNewToNat, hToBalance]
  have henoughS :
      (transferValueWord I).toNat ≤ (transferFromBalanceWord evmS).toNat := by
    simpa [evmE, hFromBalance] using henough
  have hoverS : UInt256.size ≤ transferNewToNat evmS I := by
    simpa [evmE, hNewToNat] using hover
  have hbody :
      ExecTransitionBody config contract evmS (transferStore I) transferTransition.body
        .reverted := by
    exact uniswapTransferBodyReverts_overflow evmS I
      (by simp only [evmS, initState]; exact hwv) henoughS hoverS
  exact (uniswapTransferX_overflow (g := Sat256.ofUInt256 g)
      hsz68 hsize hperm henough hover hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Short-calldata decode-failure refinement slice for `transfer(address,uint256)`.

The non-canonical branch is intentionally not claimed here; it remains explicit proof work.
-/
theorem uniswapTransferBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1234⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_transfer_none_short (I := I) hsz4 hshort
  exact (uniswapTransferX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

/-- Success `transfer(address,uint256)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapTransferBodyOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat)
    (hfit :
      transferNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
        UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ rfl hsel
  exact uniswapTransferBodyCoreOk hcode hsize hperm hwv hsz68 henough hfit
    hdispatch
    (uniswapDecode_transfer_ok hsz68)
    (uniswapReachTransferBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Short-calldata decode-failure `transfer(address,uint256)` refinement slice, packaged from
selector dispatch through the body core. -/
theorem uniswapTransferBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ rfl hsel
  exact uniswapTransferBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachTransferBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

/-- Insufficient-balance `transfer(address,uint256)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapTransferBodyRevert_insufficient
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlt : (transferFromBalanceWord
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat <
        (transferValueWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ rfl hsel
  exact uniswapTransferBodyCoreRevert_insufficient hcode hsize hwv hsz68 hlt
    hdispatch
    (uniswapDecode_transfer_ok hsz68)
    (uniswapReachTransferBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

/-- Checked-add overflow `transfer(address,uint256)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapTransferBodyRevert_overflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat)
    (hover : UInt256.size ≤
      transferNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ rfl hsel
  exact uniswapTransferBodyCoreRevert_overflow hcode hsize hperm hwv hsz68
    henough hover hdispatch
    (uniswapDecode_transfer_ok hsz68)
    (uniswapReachTransferBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapTransferBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some transferTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)).toNat
    · by_cases hfit :
        transferNewToNat (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I <
          UInt256.size
      · exact uniswapTransferBodyOk hcode hsize hperm hwv hsel hsz68
          henough hfit hdispatch hAccounts
      · exact uniswapTransferBodyRevert_overflow hcode hsize hperm hwv hsel hsz68
          henough (by omega) hdispatch hAccounts
    · exact uniswapTransferBodyRevert_insufficient hcode hsize hwv hsel hsz68
        (by omega) hdispatch hAccounts
  · exact uniswapTransferBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch

end UniswapV2Pair
