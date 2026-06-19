import Examples.ERC20.BalanceOf
import Examples.ERC20.Approve
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace ERC20

/-! ## ABI decode and source-level body for `transfer(address,uint256)` -/

/-- The raw ABI word for `transfer`'s `to` argument. -/
abbrev transferToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `transfer`'s `value` argument. -/
abbrev transferValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

abbrev transferToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (transferToWord I).toNat)

abbrev transferValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (transferValueWord I).toNat)

abbrev transferStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "to" (transferToValue I)).insert "value" (transferValueValue I)

def transferSenderSlot (evm : EVM.State) : UInt256 :=
  erc20BalanceOfSlot (.address evm.executionEnv.source)

def transferSenderSlotI (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address I.source)

def transferToSlot (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address (AccountAddress.ofNat (transferToWord I).toNat))

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
  Solm.EVM.storageLoad (transferAfterDebitState evm I) evm.executionEnv.codeOwner (transferToSlot I)

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

abbrev transferStoreNewToBalance (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (transferStoreToBalance evm I).insert "newToBalance" (transferNewToValue evm I)

def transferPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (transferAfterDebitState evm I) evm.executionEnv.codeOwner
    (transferToSlot I) (transferNewToWord evm I)

theorem transferNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    (transferNewToWord evm I).toNat = transferNewToNat evm I := by
  unfold transferNewToWord
  exact ulit_toNat' _ hfit

theorem erc20Decode_transfer_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = some (transferStore I) := by
  show decodeCalldata ["to", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferToValue, transferValueValue,
    transferToWord, transferValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "to") (y := "value") hsz68 hbig hcanon

theorem erc20Decode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "to") (y := "value") hsz4 hshort

theorem erc20Decode_transfer_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferToWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "to") (y := "value") hsz68 hbig hnc

theorem erc20Decode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferTransition.params.map Param.name)
      (transitionSignature transferTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["to", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "to") (y := "value") hbig

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

theorem transferStoreFromBalance_to_getElem? (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreFromBalance evm I)["to"]? = some (transferToValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, transferStoreFromBalance_to]

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

theorem transferStoreNewToBalance_newToBalance (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "newToBalance" =
      some (transferNewToValue evm I) := by
  rw [transferStoreNewToBalance, store_get_self]

theorem transferStoreNewToBalance_to (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "to" = some (transferToValue I) := by
  rw [transferStoreNewToBalance, store_get_ne _ _ (by decide), transferStoreToBalance,
    store_get_ne _ _ (by decide), transferStoreFromBalance_to]

theorem transferStoreNewToBalance_to_getElem? (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I)["to"]? = some (transferToValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, transferStoreNewToBalance_to]

theorem transferStoreNewToBalance_balanceOf (evm : EVM.State) (I : ExecutionEnv) :
    (transferStoreNewToBalance evm I).get? "balanceOf" = none := by
  rw [transferStoreNewToBalance, store_get_ne _ _ (by decide), transferStoreToBalance,
    store_get_ne _ _ (by decide), transferStoreFromBalance_balanceOf]

theorem evalExpr_transfer_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferStore I } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_transfer_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferStore I } evm
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_to]

theorem evalExpr_transfer_to_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_to]

theorem evalExpr_transfer_to_newToBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_to]

theorem evalExpr_transfer_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferStore I } evm
      (.var "value") = .ok (transferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_value]

def transferSenderEvaledRef (evm : EVM.State) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config { contract := erc20Contract, locals := transferStore I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, sender, envValue,
    transferSenderEvaledRef, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config { contract := erc20Contract, locals := transferStore I } evm
      (.storage (balanceOfRef sender)) = .ok (transferFromBalanceValue evm) := by
  conv_lhs => unfold evalExpr?
  rw [evalStorageRef_transfer_sender_balance]
  simp [transferSenderEvaledRef, transferSenderSlot, transferFromBalanceWord,
    EvalResult.bind, EvalResult.ofOption, bind, pure, erc20StorageLocLoad_uint256]

theorem evalStorageRef_transfer_sender_balance_fromBalance
    (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, sender, envValue,
    transferSenderEvaledRef, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

def transferToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferToWord I).toNat))] }

theorem evalStorageRef_transfer_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferToEvaledRef,
    transferToValue, valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr_transfer_to_fromBalance]

theorem evalStorageRef_transfer_to_balance_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef erc20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, transferToEvaledRef,
    transferToValue, valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr_transfer_to_newToBalance]

theorem evalExpr_transfer_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromBalanceValue, transferValueValue]
  exact henough

theorem evalExpr_transfer_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromBalanceValue, transferValueValue]
  omega

theorem evalExpr_transfer_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (.int (Int.ofNat (transferDebitWord evm I).toNat)) := by
  have hsub :
      Int.ofNat (transferFromBalanceWord evm).toNat -
          Int.ofNat (transferValueWord I).toNat =
        Int.ofNat ((transferFromBalanceWord evm).toNat - (transferValueWord I).toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat : (transferDebitWord evm I).toNat =
      (transferFromBalanceWord evm).toNat - (transferValueWord I).toNat := by
    unfold transferDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromBalanceValue, transferValueValue, hsub, htoNat]
  exact hsub

theorem transferAssignSender (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (balanceOfRef sender) (.int (Int.ofNat (transferDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferStoreFromBalance evm I },
          transferAfterDebitState evm I) := by
  unfold assignStorageRef?
  simp only [balanceOfRef]
  rw [transferStoreFromBalance_balanceOf]
  have href := evalStorageRef_transfer_sender_balance_fromBalance evm I
  simp only [balanceOfRef] at href
  rw [href]
  simp [transferAfterDebitState, transferSenderEvaledRef, transferSenderSlot,
    EvalResult.bind, EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore evm (erc20Uint256Loc (transferSenderSlot evm))
          (.int (Int.ofNat (transferDebitWord evm I).toNat)) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := transferStoreFromBalance evm I } : Frame),
          evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := transferStoreFromBalance evm I } : Frame),
        transferAfterDebitState evm I)
  rw [erc20StorageLocStore_uint256]
  simp [transferAfterDebitState]

theorem evalExpr_transfer_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I }
      (transferAfterDebitState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferToBalanceValue evm I) := by
  conv_lhs => unfold evalExpr?
  rw [evalStorageRef_transfer_to_balance_fromBalance]
  simp [transferToEvaledRef, transferToSlot, transferToBalanceWord,
    EvalResult.bind, EvalResult.ofOption, bind, pure, erc20StorageLocLoad_uint256,
    transferAfterDebit_codeOwner]

theorem evalExpr_transfer_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, transferToBalanceValue, transferValueValue, transferNewToValue,
    transferNewToNat, uint256Int, hlt]
  constructor
  · omega
  · have hfitNat :
        (transferToBalanceWord evm I).toNat + (transferValueWord I).toNat < 2 ^ 256 := by
      simpa [transferNewToNat, UInt256.size] using hfit
    omega

theorem evalExpr_transfer_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, transferToBalanceValue, transferValueValue, transferNewToValue,
    transferNewToNat, uint256Int]
  intro _
  simpa [transferNewToNat] using hge

theorem evalExpr_transfer_newToBalance_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? erc20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
      (transferAfterDebitState evm I) (.var "newToBalance") =
        .ok (transferNewToValue evm I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_newToBalance]

theorem transferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    assignStorageRef? erc20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
      (transferAfterDebitState evm I) (balanceOfRef (.var "to"))
      (transferNewToValue evm I) =
        .ok ({ contract := erc20Contract, locals := transferStoreNewToBalance evm I },
          transferPostState evm I) := by
  unfold assignStorageRef?
  simp only [balanceOfRef]
  rw [transferStoreNewToBalance_balanceOf]
  have href := evalStorageRef_transfer_to_balance_newToBalance evm (transferAfterDebitState evm I) I
  simp only [balanceOfRef] at href
  rw [href]
  simp [transferPostState, transferToEvaledRef, transferToSlot, transferNewToValue,
    EvalResult.bind, EvalResult.ofOption, bind, pure]
  change (match
      match storageLocStore (transferAfterDebitState evm I) (erc20Uint256Loc (transferToSlot I))
          (.int (Int.ofNat (transferNewToNat evm I))) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError,
      fun evm' =>
        EvalResult.ok (({ contract := erc20Contract, locals := transferStoreNewToBalance evm I } : Frame),
          evm') with
    | EvalResult.ok a, f => f a
    | EvalResult.revert, _ => EvalResult.revert
    | EvalResult.error e, _ => EvalResult.error e) =
      EvalResult.ok (({ contract := erc20Contract, locals := transferStoreNewToBalance evm I } : Frame),
        transferPostState evm I)
  rw [← transferNewToWord_toNat evm I hfit]
  rw [erc20StorageLocStore_uint256]
  simp [transferPostState, transferAfterDebit_codeOwner]

theorem erc20TransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody erc20Config erc20Contract evm (transferStore I)
      transferTransition.body
      (.returned { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
        (transferPostState evm I) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_newToBalance evm I hfit)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_newToBalance_var evm I)
      (transferAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc20TransferBodyReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    ExecTransitionBody erc20Config erc20Contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem erc20TransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecTransitionBody erc20Config erc20Contract evm (transferStore I)
      transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_transfer_require_from_true evm I henough)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_transfer_debit evm I henough) (transferAssignSender evm I)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_to_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (evalExpr_transfer_newToBalance_revert evm I hover))

/-! ## EVM scratch memory and slot facts for `transfer(address,uint256)` -/

abbrev transferSenderWord (I : ExecutionEnv) : UInt256 :=
  approveOwnerWord I

def transferTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

theorem balanceOfKeccakSlot_word (owner : UInt256)
    (hcanon : owner.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem owner).readWithPadding 0 64)))
      = erc20BalanceOfSlot (.address (AccountAddress.ofNat owner.toNat)) := by
  rw [balanceOfHashMem_read0_64]
  unfold erc20BalanceOfSlot erc20MappingSlot
  rw [erc20KeyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single owner ⟨0⟩

theorem transferSenderKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (transferSenderWord I)).readWithPadding 0 64)))
      = transferSenderSlotI I := by
  rw [balanceOfKeccakSlot_word (transferSenderWord I) (approveOwnerWord_canonical I)]
  unfold transferSenderSlotI transferSenderWord
  rw [approveOwner_ofNat]

theorem transferToKeccakSlot (I : ExecutionEnv)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (transferToWord I)).readWithPadding 0 64)))
      = transferToSlot I := by
  rw [balanceOfKeccakSlot_word (transferToWord I) hcanonTo]
  rfl

/-- Transfer stores a balance owner key at scratch offset `0x00` before it stores base slot `0`. -/
noncomputable def transferBalanceOwnerMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32

theorem transferBalanceOwnerMem_size (owner : UInt256) :
    (transferBalanceOwnerMem owner).size = 96 := by
  unfold transferBalanceOwnerMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem transferBalanceOwnerMem_writeSlot (owner : UInt256) :
    (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 (transferBalanceOwnerMem owner) 32 32 =
      balanceOfHashMem owner := by
  unfold transferBalanceOwnerMem balanceOfHashMem balanceOfBaseSlotMem
  rw [write32_eq _ solcFreePtrMem 0 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  rw [write32_eq _ solcFreePtrMem 32 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
    omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hzeroFull :
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hownerFull, hzeroFull]
  have hsolc0 : solcFreePtrMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hsolc0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, show 32 + 32 = 64 from rfl, solcFreePtrMem_size]
  have hleft0 :
      (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  rw [hleft0]
  have hleftTail :
      (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).extract 64
          (UInt256.toByteArray owner ++ solcFreePtrMem.extract 32 96).size =
        solcFreePtrMem.extract 64 96 := by
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, solcFreePtrMem_size]
    rw [extract_extract_BA]
    rfl
  rw [hleftTail]
  have hrightZero :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨0⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hrightZero, ByteArray.empty_append]
  have hrightTail :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨0⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 32
        (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨0⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).size =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
    rw [ByteArray.append_assoc]
    exact extract_append_right' _ _ _ _
      (by rw [ByteArray.size_extract, solcFreePtrMem_size]; omega)
      (by
        rw [ByteArray.size_append, ByteArray.size_extract, solcFreePtrMem_size])
  rw [hrightTail]
  exact ByteArray.append_assoc

theorem balanceOfBaseSlotMem_extract32 :
    balanceOfBaseSlotMem.extract 32 balanceOfBaseSlotMem.size =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
  unfold balanceOfBaseSlotMem
  rw [write32_eq _ solcFreePtrMem 32 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  have hzeroFull :
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hzeroFull, show 32 + 32 = 64 from rfl, solcFreePtrMem_size]
  have hrightTail :
      (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨0⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).extract 32
        (solcFreePtrMem.extract 0 32 ++ UInt256.toByteArray (⟨0⟩ : UInt256) ++
          solcFreePtrMem.extract 64 96).size =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
    rw [ByteArray.append_assoc]
    exact extract_append_right' _ _ _ _
      (by rw [ByteArray.size_extract, solcFreePtrMem_size]; omega)
      (by
        rw [ByteArray.size_append, ByteArray.size_extract, solcFreePtrMem_size])
  exact hrightTail

theorem balanceOfBaseSlotMem_extract64 :
    balanceOfBaseSlotMem.extract 64 balanceOfBaseSlotMem.size =
      solcFreePtrMem.extract 64 96 := by
  unfold balanceOfBaseSlotMem
  rw [write32_eq _ solcFreePtrMem 32 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)]
  have hzeroFull :
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  rw [hzeroFull, show 32 + 32 = 64 from rfl, solcFreePtrMem_size]
  exact extract_append_right' _ _ _ _
    (by
      rw [ByteArray.size_append, ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
      omega)
    (by rw [ByteArray.size_append])

theorem balanceOfHashMem_writeOwner_self (owner : UInt256) :
    (UInt256.toByteArray owner).write 0 (balanceOfHashMem owner) 0 32 =
      balanceOfHashMem owner := by
  unfold balanceOfHashMem
  rw [write32_eq _ _ 0 (by rw [toByteArray_size])
      (by omega)]
  rw [write32_eq _ _ 0 (by rw [toByteArray_size])
      (by omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hbase0 : balanceOfBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hownerFull, hbase0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, balanceOfBaseSlotMem_size]
  have hleftTail :
      (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).extract 32
          (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).size =
        balanceOfBaseSlotMem.extract 32 96 := by
    exact extract_append_right' (UInt256.toByteArray owner)
      (balanceOfBaseSlotMem.extract 32 96) 32
      (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).size
      (by rw [toByteArray_size])
      (by rw [ByteArray.size_append, toByteArray_size])
  have hleftZero :
      (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).extract 0 0 =
        ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hleftZero, ByteArray.empty_append, hleftTail]

theorem balanceOfHashMem_extract32 (owner : UInt256) :
    (balanceOfHashMem owner).extract 32 (balanceOfHashMem owner).size =
      balanceOfBaseSlotMem.extract 32 96 := by
  unfold balanceOfHashMem
  rw [write32_eq _ balanceOfBaseSlotMem 0 (by rw [toByteArray_size]) (by omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hbase0 : balanceOfBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hownerFull, hbase0, ByteArray.empty_append, show 0 + 32 = 32 from rfl,
    balanceOfBaseSlotMem_size]
  exact extract_append_right' (UInt256.toByteArray owner)
    (balanceOfBaseSlotMem.extract 32 96) 32
    (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).size
    (by rw [toByteArray_size])
    (by rw [ByteArray.size_append, toByteArray_size])

theorem balanceOfHashMem_writeOwner (old owner : UInt256) :
    (UInt256.toByteArray owner).write 0 (balanceOfHashMem old) 0 32 =
      balanceOfHashMem owner := by
  rw [write32_eq _ _ 0 (by rw [toByteArray_size]) (by omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hhash0 : (balanceOfHashMem old).extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hownerFull, hhash0, ByteArray.empty_append]
  rw [show 0 + 32 = 32 from rfl, balanceOfHashMem_size]
  have htail : (balanceOfHashMem old).extract 32 96 =
      balanceOfBaseSlotMem.extract 32 96 := by
    simpa [balanceOfHashMem_size] using balanceOfHashMem_extract32 old
  rw [htail]
  unfold balanceOfHashMem
  rw [write32_eq _ balanceOfBaseSlotMem 0 (by rw [toByteArray_size]) (by omega)]
  have hbase0 : balanceOfBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hownerFull, hbase0, ByteArray.empty_append, show 0 + 32 = 32 from rfl,
    balanceOfBaseSlotMem_size]

theorem balanceOfHashMem_writeSlot_self (owner : UInt256) :
    (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 (balanceOfHashMem owner) 32 32 =
      balanceOfHashMem owner := by
  unfold balanceOfHashMem
  rw [write32_eq _ balanceOfBaseSlotMem 0 (by rw [toByteArray_size])
      (by omega)]
  have hownerFull : (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hbase0 : balanceOfBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hownerFull, hbase0, ByteArray.empty_append]
  rw [balanceOfBaseSlotMem_size]
  rw [write32_eq _ _ 32 (by rw [toByteArray_size])
      (by
        rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract,
          balanceOfBaseSlotMem_size]
        omega)]
  have hleft0 :
      (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).extract 0 32 =
        UInt256.toByteArray owner := by
    rw [extract_append_left _ _ _ _ (by rw [toByteArray_size])]
    exact hownerFull
  have hleftTail :
      (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).extract 64
          (UInt256.toByteArray owner ++ balanceOfBaseSlotMem.extract 32 96).size =
        solcFreePtrMem.extract 64 96 := by
    rw [extract_append_right_window _ _ _ _ (by rw [toByteArray_size]; omega)]
    rw [ByteArray.size_append, toByteArray_size, ByteArray.size_extract, balanceOfBaseSlotMem_size]
    rw [extract_extract_BA,
      show 32 + (64 - 32) = 64 from rfl,
      show min (32 + (32 + (min 96 96 - 32) - 32)) 96 = 96 from rfl]
    simpa [balanceOfBaseSlotMem_size] using balanceOfBaseSlotMem_extract64
  have hzeroFull :
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
      rw [toByteArray_size])
  have hbase32 :
      balanceOfBaseSlotMem.extract 32 96 =
        UInt256.toByteArray (⟨0⟩ : UInt256) ++ solcFreePtrMem.extract 64 96 := by
    simpa [balanceOfBaseSlotMem_size] using balanceOfBaseSlotMem_extract32
  rw [show 0 + 32 = 32 from rfl, hleft0, hleftTail, hzeroFull, hbase32]
  exact ByteArray.append_assoc

/-- Memory after transfer's bool-return encoder overwrites the event data word at `0x80`. -/
noncomputable def transferReturnMem (toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (balanceOfReturnMem toWord value) 128 32

theorem transferReturnMem_size (toWord value : UInt256) :
    (transferReturnMem toWord value).size = 160 := by
  unfold transferReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, balanceOfReturnMem_size,
    toByteArray_size]
  omega

theorem transferReturnMem_read64 (toWord value : UInt256) :
    (transferReturnMem toWord value).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold transferReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [balanceOfReturnMem_size]; omega) (by omega),
    balanceOfReturnMem_read64]

theorem transferReturnMem_mload64 (toWord value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferReturnMem toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferReturnMem toWord value).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferReturnMem_size]; decide) (by decide)
    (transferReturnMem_read64 toWord value)

theorem transferReturnMem_read128 (toWord value : UInt256) :
    (transferReturnMem toWord value).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfReturnMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

/-- The standard Solidity panic selector word used by checked arithmetic reverts. -/
def transferPanicSelector : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def transferPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray transferPanicSelector).write 0 mem 0 32

noncomputable def transferPanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (transferPanicMem0 mem) 4 32

/-- `Error(string)` selector word (`0x08c379a0`) used by Solidity `require` reverts. -/
def transferErrorSelector : UInt256 :=
  ⟨3963877391197344453575983046348115674221700746820753546331534351508065746944⟩

/-- Padded word for `"ERC20: insufficient balance"`. -/
def transferInsufficientBalanceWord : UInt256 :=
  ⟨31354931781638678538084197150757782427756587561755285162078044387127265853440⟩

noncomputable def transferInsufficientSelectorMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray transferErrorSelector).write 0 (balanceOfHashMem owner) 128 32

noncomputable def transferInsufficientOffsetMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (transferInsufficientSelectorMem owner) 132 32

noncomputable def transferInsufficientLengthMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨27⟩ : UInt256)).write 0
    (transferInsufficientOffsetMem owner) 164 32

noncomputable def transferInsufficientStringMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray transferInsufficientBalanceWord).write 0
    (transferInsufficientLengthMem owner) 196 32

theorem transferInsufficientSelectorMem_size (owner : UInt256) :
    (transferInsufficientSelectorMem owner).size = 160 := by
  unfold transferInsufficientSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfHashMem_size]; omega)
      (by rw [balanceOfHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem transferInsufficientOffsetMem_size (owner : UInt256) :
    (transferInsufficientOffsetMem owner).size = 164 := by
  unfold transferInsufficientOffsetMem
  rw [write32_eq _ _ 132 (by rw [toByteArray_size])
      (by rw [transferInsufficientSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientSelectorMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientLengthMem_size (owner : UInt256) :
    (transferInsufficientLengthMem owner).size = 196 := by
  unfold transferInsufficientLengthMem
  rw [write32_eq _ _ 164 (by rw [toByteArray_size])
      (by rw [transferInsufficientOffsetMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientOffsetMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientStringMem_size (owner : UInt256) :
    (transferInsufficientStringMem owner).size = 228 := by
  unfold transferInsufficientStringMem
  rw [write32_eq _ _ 196 (by rw [toByteArray_size])
      (by rw [transferInsufficientLengthMem_size]),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferInsufficientLengthMem_size,
    toByteArray_size]
  omega

theorem transferInsufficientSelectorMem_read64 (owner : UInt256) :
    (transferInsufficientSelectorMem owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientSelectorMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfHashMem_size]; omega)
      (by rw [balanceOfHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, balanceOfHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [balanceOfHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by rw [balanceOfHashMem_size])]
  exact balanceOfHashMem_read64 owner

theorem transferInsufficientOffsetMem_read64 (owner : UInt256) :
    (transferInsufficientOffsetMem owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientOffsetMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientSelectorMem_size]; omega) (by omega),
    transferInsufficientSelectorMem_read64]

theorem transferInsufficientLengthMem_read64 (owner : UInt256) :
    (transferInsufficientLengthMem owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientLengthMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientOffsetMem_size]) (by omega),
    transferInsufficientOffsetMem_read64]

theorem transferInsufficientStringMem_read64 (owner : UInt256) :
    (transferInsufficientStringMem owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold transferInsufficientStringMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
      (by rw [transferInsufficientLengthMem_size]) (by omega),
    transferInsufficientLengthMem_read64]

theorem transferInsufficientStringMem_mload64 (owner : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (transferInsufficientStringMem owner).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((transferInsufficientStringMem owner).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [transferInsufficientStringMem_size]; decide) (by decide)
    (transferInsufficientStringMem_read64 owner)

end ERC20

namespace Reasoning.Theory

theorem gt_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.GT, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.gt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.GT, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_gt s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem ugt_zero {a b : UInt256} (h : a.toNat ≤ b.toNat) : UInt256.gt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a > b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ (a > b) from by
    show ¬ (a.toNat > b.toNat)
    omega)]
  rfl

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.gt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.GT, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.gt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => Reasoning.Theory.gt_xstep hc hp hdec hs hov)

theorem RD.erc20PanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {R : List UInt256} {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2507⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev erc20Bytecode g s0 := by
  have rd2508 := evm_run h with [ jumpdest ]
  have rd2541 := rd2508.pushConst ERC20.transferPanicSelector
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2543 := evm_run rd2541 with [
    push0,
    raw mstore 0 (ERC20.transferPanicMem0 mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩ ]
  have rd2548 := evm_run rd2543 with [
    raw mstore 0 (ERC20.transferPanicMem mem) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, push0 ]
  exact rd2548.rev 0 (by decide) mem_cost (by evm_ov)

end Reasoning.Reach

namespace ERC20

/-! ## EVM trace for `transfer(address,uint256)` -/

/-- Wrapper pc 274 sets up calldata bounds for `transfer(address,uint256)` and jumps to the
    shared `(address,uint256)` tuple decoder at pc 1945. -/
theorem erc20TransferX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1945⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨295⟩, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨300⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨295⟩, swap2, swap1, push2 ⟨1945⟩, jump erc20_jd ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem erc20TransferX_dec1874_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨1980⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
          ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨295⟩, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc20TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨1980⟩, dup6, dup3, dup7, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `to` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec1980` chain. -/
theorem erc20TransferX_dec1980 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1980⟩
        [transferToWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨295⟩, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20TransferX_dec1874_to (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem erc20TransferX_dec1925_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1925⟩
        [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨1997⟩, ⟨32⟩, ⟨0⟩,
          transferToWord I, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨295⟩, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20TransferX_dec1980 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨1997⟩, dup6, dup3, dup7,
    add, push2 ⟨1925⟩, jump erc20_jd ]⟩

theorem erc20TransferX_dec1903_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1903⟩
        [transferValueWord I, ⟨1939⟩, transferValueWord I, ⟨4⟩ + ⟨32⟩,
          UInt256.ofNat I.calldata.size, ⟨1997⟩, ⟨32⟩, ⟨0⟩, transferToWord I,
          ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨295⟩, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20TransferX_dec1925_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨1939⟩, dup2,
    push2 ⟨1903⟩, jump erc20_jd ]⟩

theorem erc20TransferX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1365⟩
        [transferValueWord I, transferToWord I, ⟨300⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd1903⟩ := erc20TransferX_dec1903_value (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have rd1894 := evm_run rd1903 with [
    jumpdest, push2 ⟨1912⟩, dup2, push2 ⟨1894⟩, jump erc20_jd ]
  have rd1912 := rd1894.erc20Routine0766 erc20_jd (by evm_ov)
  have hclean : UInt256.eq (transferValueWord I) (transferValueWord I) = ⟨1⟩ :=
    erc20Ueq_self (transferValueWord I)
  have rd1939 := evm_run rd1912 with [
    jumpdest, dup2, eq, push2 ⟨1922⟩, jumpiT (by rw [hclean]; decide) erc20_jd,
    jumpdest, pop, jump erc20_jd ]
  exact ⟨_, _, evm_run rd1939 with [
    jumpdest, swap3, swap2, pop, pop, jump erc20_jd,
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump erc20_jd,
    jumpdest, push2 ⟨1365⟩, jump erc20_jd ]⟩

/-- The transfer body computes `balanceOf[msg.sender]`, checks `value <= fromBalance`, and
    reaches the success branch with the scratch false return word still on the stack. -/
theorem erc20TransferX_afterRequire {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1493⟩
        [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
        (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd1365⟩ := erc20TransferX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hslot := transferSenderKeccakSlot I
  have rd1415₀ := evm_run rd1365 with [
    jumpdest, push0, dup2, push0, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1415 := rd1415₀
  rw [hsenderCleanL, hsenderCleanL] at rd1415
  obtain ⟨_, _, rd1428⟩ := RD.erc20MappingHashSuffix rd1415 erc20_mapping_hash_wf
    (by rfl) (transferBalanceOwnerMem_writeSlot (transferSenderWord I)) hslot (by evm_ov)
  obtain ⟨k1, C1, rd1429₀⟩ := rd1428.sload (by decide) (by evm_ov)
  have rd1429 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1429⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, initState]
      using rd1429₀
  have hlt : UInt256.lt (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I))
      (transferValueWord I) = ⟨0⟩ := ult_zero henough
  exact ⟨_, _, evm_run rd1429 with [
    lt, iszero, push2 ⟨1493⟩, jumpiT (by rw [hlt]; decide) erc20_jd ]⟩

theorem erc20TransferX_insufficient {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat <
      (transferValueWord I).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd1365⟩ := erc20TransferX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo hreach
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hslot := transferSenderKeccakSlot I
  have rd1415₀ := evm_run rd1365 with [
    jumpdest, push0, dup2, push0, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1415 := rd1415₀
  rw [hsenderCleanL, hsenderCleanL] at rd1415
  obtain ⟨_, _, rd1428⟩ := RD.erc20MappingHashSuffix rd1415 erc20_mapping_hash_wf
    (by rfl) (transferBalanceOwnerMem_writeSlot (transferSenderWord I)) hslot (by evm_ov)
  obtain ⟨k1, C1, rd1429₀⟩ := rd1428.sload (by decide) (by evm_ov)
  have rd1429 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1429⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, initState]
      using rd1429₀
  have hltw : UInt256.lt (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I))
      (transferValueWord I) = ⟨1⟩ := ult_one hlt
  have rd1430₀ := evm_run rd1429 with [ lt ]
  have rd1430 := rd1430₀
  rw [hltw] at rd1430
  have rd1431₀ := evm_run rd1430 with [ iszero ]
  have rd1431 := rd1431₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1431
  have rd1435 := evm_run rd1431 with [
    push2 ⟨1493⟩, jumpiNT (by decide) ]
  have rd1438 := evm_run rd1435 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferSenderWord I))
      (by decide) (by evm_ov) ]
  have rd1471 := rd1438.pushConst transferErrorSelector (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd1473 := evm_run rd1471 with [
    dup2,
    raw mstore 6 (transferInsufficientSelectorMem (transferSenderWord I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2477 := evm_run rd1473 with [
    push1 ⟨4⟩, add, push2 ⟨1484⟩, swap1, push2 ⟨2477⟩, jump erc20_jd ]
  have rd2492 := evm_run rd2477 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, dup2, dup2, sub,
    push0, dup4, add,
    raw mstore 3 (transferInsufficientOffsetMem (transferSenderWord I)) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov) ]
  have rd2443 := evm_run rd2492 with [
    push2 ⟨2500⟩, dup2, push2 ⟨2443⟩, jump erc20_jd ]
  have rd2283 := evm_run rd2443 with [
    jumpdest, push0, push2 ⟨2455⟩, push1 ⟨27⟩, dup4, push2 ⟨2283⟩,
    jump erc20_jd ]
  have rd2455 := evm_run rd2283 with [
    jumpdest, push0, dup3, dup3,
    raw mstore 3 (transferInsufficientLengthMem (transferSenderWord I)) (UInt256.ofNat 7)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop, swap3, swap2, pop, pop,
    jump erc20_jd ]
  have rd2403 := evm_run rd2455 with [
    jumpdest, swap2, pop, push2 ⟨2466⟩, dup3, push2 ⟨2403⟩, jump erc20_jd ]
  have rd2404 := evm_run rd2403 with [ jumpdest ]
  have rd2437 := rd2404.pushConst transferInsufficientBalanceWord
    (width := 32) (op := .PUSH32) (by decide) (by decide) (by evm_ov)
  have rd2466 := evm_run rd2437 with [
    push0, dup3, add,
    raw mstore 3 (transferInsufficientStringMem (transferSenderWord I)) (UInt256.ofNat 8)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, jump erc20_jd ]
  have rd2500 := evm_run rd2466 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop, swap2, swap1, pop,
    jump erc20_jd ]
  have rd1484 := evm_run rd2500 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump erc20_jd ]
  have rd1492 := evm_run rd1484 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (transferInsufficientStringMem_mload64 (transferSenderWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact rd1492.rev 0 (by decide) mem_cost (by evm_ov)

theorem erc20RoutineCheckedSub {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2552⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  have rd2562₀ := evm_run h with [
    jumpdest, push0, push2 ⟨2562⟩, dup3, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2562 := rd2562₀.erc20Routine0766 erc20_jd (by evm_ov)
  have rd2573₀ := evm_run rd2562 with [
    jumpdest, swap2, pop, push2 ⟨2573⟩, dup4, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2573 := rd2573₀.erc20Routine0766 erc20_jd (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd2583 := evm_run rd2573 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2 ]
  have rd2584₀ := evm_run rd2583 with [ gt ]
  have rd2584 := rd2584₀
  rw [hgt] at rd2584
  have rd2585₀ := evm_run rd2584 with [ iszero ]
  have rd2585 := rd2585₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2585
  have rd2597 := evm_run rd2585 with [
    push2 ⟨2597⟩, jumpiT one_ne_zero_uint erc20_jd ]
  exact ⟨_, _, evm_run rd2597 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

theorem erc20RoutineCheckedSub_underflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2552⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 3)
      rdata acc k C)
    (hlt : a.toNat < b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev erc20Bytecode g s0 := by
  have rd2562₀ := evm_run h with [
    jumpdest, push0, push2 ⟨2562⟩, dup3, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2562 := rd2562₀.erc20Routine0766 erc20_jd (by evm_ov)
  have rd2573₀ := evm_run rd2562 with [
    jumpdest, swap2, pop, push2 ⟨2573⟩, dup4, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2573 := rd2573₀.erc20Routine0766 erc20_jd (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd2583 := evm_run rd2573 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2 ]
  have rd2584₀ := evm_run rd2583 with [ gt ]
  have rd2584 := rd2584₀
  rw [hgt] at rd2584
  have rd2585₀ := evm_run rd2584 with [ iszero ]
  have rd2585 := rd2585₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2585
  have rd2589 := evm_run rd2585 with [
    push2 ⟨2597⟩, jumpiNT (by decide) ]
  have rd2507 := evm_run rd2589 with [
    push2 ⟨2596⟩, push2 ⟨2507⟩, jump erc20_jd ]
  exact rd2507.erc20PanicOverflowRevert (by evm_ov)

theorem erc20RoutineCheckedAdd {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2603⟩ (a :: b :: ret :: R) mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J erc20Bytecode 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD erc20Bytecode ee g s0 ret ((a + b) :: R) mem aw rdata acc k' C' := by
  have rd2613₀ := evm_run h with [
    jumpdest, push0, push2 ⟨2613⟩, dup3, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2613 := rd2613₀.erc20Routine0766 erc20_jd (by evm_ov)
  have rd2624₀ := evm_run rd2613 with [
    jumpdest, swap2, pop, push2 ⟨2624⟩, dup4, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2624 := rd2624₀.erc20Routine0766 erc20_jd (by evm_ov)
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt a (a + b) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [haddNat]; omega)
  have rd2634 := evm_run rd2624 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3 ]
  have rd2635₀ := evm_run rd2634 with [ gt ]
  have rd2635 := rd2635₀
  rw [hgt] at rd2635
  have rd2636₀ := evm_run rd2635 with [ iszero ]
  have rd2636 := rd2636₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2636
  have rd2648 := evm_run rd2636 with [
    push2 ⟨2648⟩, jumpiT one_ne_zero_uint erc20_jd ]
  exact ⟨_, _, evm_run rd2648 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

theorem erc20RoutineCheckedAdd_overflow {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc20Bytecode ee g s0 ⟨2603⟩ (a :: b :: ret :: R) mem (UInt256.ofNat 3)
      rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev erc20Bytecode g s0 := by
  have rd2613₀ := evm_run h with [
    jumpdest, push0, push2 ⟨2613⟩, dup3, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2613 := rd2613₀.erc20Routine0766 erc20_jd (by evm_ov)
  have rd2624₀ := evm_run rd2613 with [
    jumpdest, swap2, pop, push2 ⟨2624⟩, dup4, push2 ⟨1894⟩, jump erc20_jd ]
  have rd2624 := rd2624₀.erc20Routine0766 erc20_jd (by evm_ov)
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hgt : UInt256.gt a (a + b) = ⟨1⟩ := by
    show UInt256.fromBool (decide (a > a + b)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show a.toNat > (a + b).toNat
      rw [haddNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd2634 := evm_run rd2624 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3 ]
  have rd2635₀ := evm_run rd2634 with [ gt ]
  have rd2635 := rd2635₀
  rw [hgt] at rd2635
  have rd2636₀ := evm_run rd2635 with [ iszero ]
  have rd2636 := rd2636₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2636
  have rd2640 := evm_run rd2636 with [
    push2 ⟨2648⟩, jumpiNT (by decide) ]
  have rd2507 := evm_run rd2640 with [
    push2 ⟨2647⟩, push2 ⟨2507⟩, jump erc20_jd ]
  exact rd2507.erc20PanicOverflowRevert (by evm_ov)

theorem erc20TransferX_afterDebit {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1576⟩
        [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
        (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd1493⟩ := erc20TransferX_afterRequire (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonTo henough hreach
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have hslot := transferSenderKeccakSlot I
  have rd1517₀ := evm_run rd1493 with [
    jumpdest, dup2, push0, push0, caller, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1517 := rd1517₀
  rw [hsenderCleanL, hsenderCleanL] at rd1517
  obtain ⟨_, _, rd1530₀⟩ := RD.erc20MappingHashSuffix rd1517 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner_self (transferSenderWord I))
    (balanceOfHashMem_writeSlot_self (transferSenderWord I)) hslot (by evm_ov)
  have rd1530 := evm_run rd1530₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1559₀⟩ := rd1530.sload (by decide) (by evm_ov)
  have rd1559 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1559⟩
      [transferFromBalanceWord (initState cA gh bl σ σ₀ g A I), transferValueWord I,
        ⟨0⟩, transferSenderSlotI I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferSenderWord I)) (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      k1 C1 := by
    simpa [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, initState,
      Solm.EVM.storageLoad]
      using rd1559₀
  have rd2552 := evm_run rd1559 with [
    push2 ⟨1568⟩, swap2, swap1, push2 ⟨2552⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1568₀⟩ := erc20RoutineCheckedSub rd2552 henough erc20_jd
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hdebit :
      UInt256.sub (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I))
          (transferValueWord I) =
        transferDebitWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [usub_toNat henough]
    unfold transferDebitWord
    rw [ulit_toNat' _ (lt_of_le_of_lt
      (Nat.sub_le (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat
        (transferValueWord I).toNat)
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).val.isLt)]
  have rd1568 := rd1568₀
  rw [hdebit] at rd1568
  have rd1575 := evm_run rd1568 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1575s⟩ := rd1575.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1575s with [ pop ]⟩

theorem erc20TransferX_afterCredit {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1658⟩
        [⟨0⟩, transferValueWord I, transferToWord I, ⟨300⟩, sel]
        (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
            (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
          (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd1576⟩ := erc20TransferX_afterDebit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo henough hreach
  have htoCleanL : UInt256.land erc20AddrMask (transferToWord I) = transferToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferToKeccakSlot I hcanonTo
  have rd1624₀ := evm_run rd1576 with [
    dup2, push0, push0, dup6, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1624 := rd1624₀
  rw [htoCleanL, htoCleanL] at rd1624
  obtain ⟨_, _, rd1640₀⟩ := RD.erc20MappingHashSuffix rd1624 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner (transferSenderWord I) (transferToWord I))
    (balanceOfHashMem_writeSlot_self (transferToWord I)) hslot (by evm_ov)
  have rd1640 := evm_run rd1640₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1641₀⟩ := rd1640.sload (by decide) (by evm_ov)
  have rd1641 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1641⟩
      [transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I, transferValueWord I,
        ⟨0⟩, transferToSlot I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferToBalanceWord, transferAfterDebitState, transferSenderSlot,
      transferSenderSlotI, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, erc20StorageStore_accountMap]
      using rd1641₀
  have rd2603 := evm_run rd1641 with [
    push2 ⟨1650⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd1650₀⟩ := erc20RoutineCheckedAdd rd2603
    (by simpa [transferNewToNat] using hfit)
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have hnew :
      transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I + transferValueWord I =
        transferNewToWord (initState cA gh bl σ σ₀ g A I) I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by simpa [transferNewToNat] using hfit)]
    unfold transferNewToWord
    rw [ulit_toNat' _ hfit]
    rfl
  have rd1650 := rd1650₀
  rw [hnew] at rd1650
  have rd1656 := evm_run rd1650 with [
    jumpdest, swap3, pop, pop, dup2, swap1 ]
  obtain ⟨k3, C3, rd1656s⟩ := rd1656.sstore hperm (by decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1656s with [ pop ]⟩

theorem erc20TransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hover : UInt256.size ≤ transferNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd1576⟩ := erc20TransferX_afterDebit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo henough hreach
  have htoCleanL : UInt256.land erc20AddrMask (transferToWord I) = transferToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have hslot := transferToKeccakSlot I hcanonTo
  have rd1624₀ := evm_run rd1576 with [
    dup2, push0, push0, dup6, push20 erc20AddrMask, and,
    push20 erc20AddrMask, and ]
  have rd1624 := rd1624₀
  rw [htoCleanL, htoCleanL] at rd1624
  obtain ⟨_, _, rd1640₀⟩ := RD.erc20MappingHashSuffix rd1624 erc20_mapping_hash_wf
    (balanceOfHashMem_writeOwner (transferSenderWord I) (transferToWord I))
    (balanceOfHashMem_writeSlot_self (transferToWord I)) hslot (by evm_ov)
  have rd1640 := evm_run rd1640₀ with [ push0, dup3, dup3 ]
  obtain ⟨k1, C1, rd1641₀⟩ := rd1640.sload (by decide) (by evm_ov)
  have rd1641 : RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1641⟩
      [transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I, transferValueWord I,
        ⟨0⟩, transferToSlot I, transferValueWord I, ⟨0⟩, transferValueWord I,
        transferToWord I, ⟨300⟩, sel]
      (balanceOfHashMem (transferToWord I)) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k1 C1 := by
    simpa [transferToBalanceWord, transferAfterDebitState, transferSenderSlot,
      transferSenderSlotI, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, erc20StorageStore_accountMap]
      using rd1641₀
  have rd2603 := evm_run rd1641 with [
    push2 ⟨1650⟩, swap2, swap1, push2 ⟨2603⟩, jump erc20_jd ]
  exact erc20RoutineCheckedAdd_overflow rd2603
    (by simpa [transferNewToNat] using hover)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20X_transfer {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd1658⟩ := erc20TransferX_afterCredit (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hperm hcanonTo henough hfit hreach
  have hsenderCleanL : UInt256.land erc20AddrMask (transferSenderWord I) = transferSenderWord I :=
    erc20AddrMask_clean_left (approveOwnerWord_canonical I)
  have htoCleanL : UInt256.land erc20AddrMask (transferToWord I) = transferToWord I :=
    erc20AddrMask_clean_left hcanonTo
  have rd1704₀ := evm_run rd1658 with [
    dup3, push20 erc20AddrMask, and, caller, push20 erc20AddrMask, and ]
  have rd1704 := rd1704₀
  rw [htoCleanL, hsenderCleanL] at rd1704
  have rd1737₀ := rd1704.pushConst transferTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd2073 := evm_run rd1737₀ with [
    dup5, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (transferToWord I))
      (by decide) (by evm_ov),
    push2 ⟨1750⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k1, C1, rd1750⟩ := erc20RoutineEncodeUint256FromMem
    (val := transferValueWord I) (ret := ⟨1750⟩)
    (R := [transferTransferTopic, transferSenderWord I, transferToWord I, ⟨0⟩,
      transferValueWord I, transferToWord I, ⟨300⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1758 := evm_run rd1750 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd1759 := rd1758.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by evm_ov)
  have rd300 := evm_run rd1759 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump erc20_jd ]
  have rd2033 := evm_run rd300 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    push2 ⟨313⟩, swap2, swap1, push2 ⟨2033⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd313⟩ := erc20RoutineEncodeBoolFromMem
    (val := (⟨1⟩ : UInt256)) (ret := ⟨313⟩) (R := [sel])
    rd2033
    (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide])
    erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd313 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (transferReturnMem_mload64 (transferToWord I) (transferValueWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        exact transferReturnMem_read128 (transferToWord I) (transferValueWord I))
      (by evm_ov) ]

theorem erc20TransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc20TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨1966⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20TransferX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k, C, rd⟩ := erc20TransferX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1967⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨1966⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20TransferX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (transferToWord I)
      (UInt256.land (transferToWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20TransferX_dec1874_to (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz68 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20TransferSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some transferTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) :=
    (erc20ByteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList]
  change dispatchList
    [approveTransition, totalSupplyTransition, transferFromTransition, balanceOfTransition,
      transferTransition, allowanceTransition] cd = some transferTransition
  rw [dispatchList_cons, selectorOf, erc20ApproveSelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20TotalSupplySelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20TransferFromSelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20BalanceOfSelectorBytes]
  rw [if_neg (by rw [hcd]; decide)]
  rw [dispatchList_cons, selectorOf, erc20TransferSelectorBytes]
  rw [if_pos (by rw [hcd]; decide)]

theorem erc20TransferBodyCore {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl σ σ₀ g A I := by
  have hsz4 := erc20TransferSelector_size hsel
  have hd := erc20Dispatch_transfer (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonTo : (transferToWord I).toNat < EVM.addressModulus
      · have hdec := erc20Decode_transfer_ok (I := I) hsz68 hbig hcanonTo
        by_cases henough : (transferValueWord I).toNat ≤
            (transferFromBalanceWord
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)).toNat
        · by_cases hfit :
            transferNewToNat (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I <
              UInt256.size
          · have hbody := erc20TransferBodyReturns
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) henough hfit
            exact (erc20X_transfer (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanonTo henough hfit hreach)
              |>.reEquivExecutionGen hcode hd hdec hbody
                (by
                  simp [transferPostState, transferAfterDebitState, transferSenderSlot,
                    transferSenderSlotI, initState, erc20StorageStore_createdAccounts,
                    erc20StorageStore_accountMap])
                (returnEquiv_of_encode erc20BoolTrueReturnEncoding)
          · have hover :
              UInt256.size ≤
                transferNewToNat (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I := by
              omega
            have hbody := erc20TransferBodyReverts_overflow
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) henough hover
            exact (erc20TransferX_overflow (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hperm hcanonTo henough hover hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hlt :
            (transferFromBalanceWord
                (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)).toNat <
              (transferValueWord I).toNat := by
            omega
          have hbody := erc20TransferBodyReverts_insufficient
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hlt
          exact (erc20TransferX_insufficient (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonTo hlt hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := erc20Decode_transfer_none_noncanon (I := I) hsz68 hbig hcanonTo
        have hnc : UInt256.eq (transferToWord I)
            (UInt256.land (transferToWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanonTo (erc20Word_canonical_of_clean he))
        exact (erc20TransferX_noncanon_to (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_transfer_none_huge (I := I) hbigge
      exact (erc20TransferX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := erc20Decode_transfer_none_short (I := I) hsz4 hshort
    exact (erc20TransferX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20
