import Examples.VyperERC20.Approve
import Reasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

/-! ## Source side for `transfer(address,uint256)` under the Vyper storage layout -/

abbrev transferToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev transferValueWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

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
    (hsz68 : 68 ≤ I.calldata.size)
    (hcanon : (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferTransition.params.map Param.name)
      (transitionSignature ERC20.transferTransition).paramTypes I.calldata = some (transferStore I) := by
  show decodeCalldataWithMode DecodeMode.vyper ["to", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, transferStore, transferToValue, transferValueValue,
    transferToWord, transferValueWord, calldataWord]
    using decodeCalldataWithMode_vyper_addr_uint256_ok
      (cd := I.calldata) (x := "to") (y := "value") hsz68 hcanon

theorem erc20Decode_transfer_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferTransition.params.map Param.name)
      (transitionSignature ERC20.transferTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["to", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256]
    using decodeCalldataWithMode_vyper_addr_uint256_none_short
      (cd := I.calldata) (x := "to") (y := "value") hsz4 hshort

theorem erc20Decode_transfer_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size)
    (hnc : ¬ (transferToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.transferTransition.params.map Param.name)
      (transitionSignature ERC20.transferTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["to", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, transferToWord]
    using decodeCalldataWithMode_vyper_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "to") (y := "value") hsz68 hnc

theorem erc20Decode_transfer_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (ERC20.transferTransition.params.map Param.name)
      (transitionSignature ERC20.transferTransition).paramTypes I.calldata = none := by
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
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferStore I } evm
      sender = .ok (.address evm.executionEnv.source) := by
  simp [sender, ERC20.sender, evalExpr?, envValue, pure]

theorem evalExpr_transfer_to (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferStore I } evm
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_to]

theorem evalExpr_transfer_to_fromBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreFromBalance_to]

theorem evalExpr_transfer_to_newToBalance (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I } evm'
      (.var "to") = .ok (transferToValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_to]

theorem evalExpr_transfer_value (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferStore I } evm
      (.var "value") = .ok (transferValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStore_value]

def transferSenderEvaledRef (evm : EVM.State) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address evm.executionEnv.source)] }

theorem evalStorageRef_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config { contract := erc20Contract, locals := transferStore I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef, sender, ERC20.sender,
    envValue, transferSenderEvaledRef, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_transfer_sender_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config { contract := erc20Contract, locals := transferStore I } evm
      (.storage (balanceOfRef sender)) = .ok (transferFromBalanceValue evm) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := transferStore_balanceOf I)
    (her := evalStorageRef_transfer_sender_balance evm I)
    (hty := by simp [storageTypeAt?, transferSenderEvaledRef, erc20Contract, ERC20.erc20Contract,
       ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_balanceOf (.address evm.executionEnv.source))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferSenderEvaledRef, transferSenderSlot, transferFromBalanceWord]

theorem evalStorageRef_transfer_sender_balance_fromBalance
    (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (balanceOfRef sender) = .ok (transferSenderEvaledRef evm) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef, sender, ERC20.sender,
    envValue, transferSenderEvaledRef, valueToKey?, EvalResult.seqList, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

def transferToEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (transferToWord I).toNat))] }

theorem evalStorageRef_transfer_to_balance_fromBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef, transferToEvaledRef,
    transferToValue, valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr_transfer_to_fromBalance]

theorem evalStorageRef_transfer_to_balance_newToBalance
    (evm evm' : EVM.State) (I : ExecutionEnv) :
    evalStorageRef vyperERC20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I } evm'
      (balanceOfRef (.var "to")) = .ok (transferToEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef, transferToEvaledRef,
    transferToValue, valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr_transfer_to_newToBalance]

theorem evalExpr_transfer_require_from_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromBalanceValue, transferValueValue]
  exact henough

theorem evalExpr_transfer_require_from_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreFromBalance_fromBalance, transferStoreFromBalance_value]
  simp [evalBinaryOp?, transferFromBalanceValue, transferValueValue]
  omega

theorem evalExpr_transfer_debit (evm : EVM.State) (I : ExecutionEnv)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat) :
    evalExpr? vyperERC20Config
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
    assignStorageRef? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I } evm
      .storage (balanceOfRef sender) (.int (Int.ofNat (transferDebitWord evm I).toNat)) =
        .ok ({ contract := erc20Contract, locals := transferStoreFromBalance evm I },
          transferAfterDebitState evm I) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256Storage)
      (hbase := transferStoreFromBalance_balanceOf evm I)
      (her := evalStorageRef_transfer_sender_balance_fromBalance evm I)
      (hty := by simp [storageTypeAt?, transferSenderEvaledRef, erc20Contract, ERC20.erc20Contract,
         ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?])
      (hloc := vyperERC20Config_storage_balanceOf (.address evm.executionEnv.source))
  rw [vyperERC20StorageLocStore_uint256]
  simp [transferAfterDebitState, transferSenderSlot]

theorem evalExpr_transfer_to_balance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreFromBalance evm I }
      (transferAfterDebitState evm I) (.storage (balanceOfRef (.var "to"))) =
        .ok (transferToBalanceValue evm I) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := transferStoreFromBalance_balanceOf evm I)
    (her := evalStorageRef_transfer_to_balance_fromBalance evm (transferAfterDebitState evm I) I)
    (hty := by simp [storageTypeAt?, transferToEvaledRef, erc20Contract, ERC20.erc20Contract,
       ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?])
    (hloc := vyperERC20Config_storage_balanceOf
      (.address (AccountAddress.ofNat (transferToWord I).toNat)))]
  rw [vyperERC20StorageLocLoad_uint256]
  simp [transferToEvaledRef, transferToSlot, transferToBalanceWord, transferAfterDebit_codeOwner]

theorem evalExpr_transfer_newToBalance (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (ERC20.valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) =
        .ok (transferNewToValue evm I) := by
  have hlt : ¬ Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hnonneg : ¬ Int.ofNat (transferNewToNat evm I) < 0 := by
    exact not_lt_of_ge (Int.ofNat_nonneg _)
  simp only [ERC20.valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, transferToBalanceValue, transferValueValue, transferNewToValue,
    transferNewToNat, uint256Int, ERC20.uint256Int, hlt, hnonneg]
  constructor
  · exact Int.add_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  · have hfitNat :
        (transferToBalanceWord evm I).toNat + (transferValueWord I).toNat < 2 ^ 256 := by
      simpa [transferNewToNat, UInt256.size] using hfit
    exact Int.ofNat_lt.mpr hfitNat

theorem evalExpr_transfer_newToBalance_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreToBalance evm I }
      (transferAfterDebitState evm I)
      (ERC20.valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))) = .revert := by
  have hge : Int.ofNat (transferNewToNat evm I) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [ERC20.valueInUInt256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [transferStoreToBalance_toBalance, transferStoreToBalance_value]
  simp [evalBinaryOp?, transferToBalanceValue, transferValueValue, transferNewToValue,
    transferNewToNat, uint256Int, ERC20.uint256Int]
  intro _
  simpa [transferNewToNat] using hge

theorem evalExpr_transfer_newToBalance_var (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
      (transferAfterDebitState evm I) (.var "newToBalance") =
        .ok (transferNewToValue evm I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [transferStoreNewToBalance_newToBalance]

theorem transferAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : transferNewToNat evm I < UInt256.size) :
    assignStorageRef? vyperERC20Config
      { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
      (transferAfterDebitState evm I) .storage (balanceOfRef (.var "to"))
      (transferNewToValue evm I) =
        .ok ({ contract := erc20Contract, locals := transferStoreNewToBalance evm I },
          transferPostState evm I) := by
  have hbase := transferStoreNewToBalance_balanceOf evm I
  have her :=
    evalStorageRef_transfer_to_balance_newToBalance evm (transferAfterDebitState evm I) I
  have hty :
      storageTypeAt? erc20Contract.storage (transferToEvaledRef I) =
        some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, transferToEvaledRef, erc20Contract, ERC20.erc20Contract,
      ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?]
  have hloc :
      vyperERC20Config.storage.layout (transferToEvaledRef I) =
        fun _ => some (vyperUint256Loc (transferToSlot I)) := by
    simpa [transferToEvaledRef, transferToSlot] using
      vyperERC20Config_storage_balanceOf
        (.address (AccountAddress.ofNat (transferToWord I).toNat))
  simp only [balanceOfRef]
  refine assignStorageRef_storage_scalar
    (cfg := vyperERC20Config)
    (solm := { contract := erc20Contract, locals := transferStoreNewToBalance evm I })
    (evm := transferAfterDebitState evm I)
    (evm' := transferPostState evm I)
    (slot := { base := "balanceOf", steps := [.mindex (.var "to")] })
    (er := transferToEvaledRef I)
    (ty := uint256Storage)
    (loc := vyperUint256Loc (transferToSlot I))
    (n := Int.ofNat (transferNewToNat evm I))
    hbase her hty hloc ?_
  rw [← transferNewToWord_toNat evm I hfit]
  rw [vyperERC20StorageLocStore_uint256]
  simp [transferPostState, transferToSlot, transferAfterDebit_codeOwner]

theorem erc20TransferBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hfit : transferNewToNat evm I < UInt256.size) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferStore I)
      ERC20.transferTransition.body
      (.returned { contract := erc20Contract, locals := transferStoreNewToBalance evm I }
        (transferPostState evm I) (some [(.bool true)])) := by
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
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem erc20TransferBodyReverts_insufficient (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlt : (transferFromBalanceWord evm).toNat < (transferValueWord I).toNat) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferStore I)
      ERC20.transferTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_transfer_sender_balance evm I)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_transfer_require_from_false evm I hlt))

theorem erc20TransferBodyReverts_overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (henough : (transferValueWord I).toNat ≤ (transferFromBalanceWord evm).toNat)
    (hover : UInt256.size ≤ transferNewToNat evm I) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (transferStore I)
      ERC20.transferTransition.body .reverted := by
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

/-! ## Vyper bytecode memory for the `transfer` success path -/

def transferSelectorWord : UInt256 :=
  ⟨0xa9059cbb⟩

def transferEventTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

def transferDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 811 ByteArray.empty 30 2

theorem transferDispatchMem_size : transferDispatchMem.size = 32 := by
  native_decide

def transferToArgMem (dst : UInt256) : ByteArray :=
  (UInt256.toByteArray dst).write 0 transferDispatchMem 64 32

noncomputable def transferSenderKeyMem (dst owner : UInt256) : ByteArray :=
  wordAt32Mem owner (transferToArgMem dst)

noncomputable def transferSenderHashMem (dst owner : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (transferSenderKeyMem dst owner)

noncomputable def transferSenderKeyMemAgain (dst owner : UInt256) : ByteArray :=
  wordAt32Mem owner (transferSenderHashMem dst owner)

noncomputable def transferSenderHashMemAgain (dst owner : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (transferSenderKeyMemAgain dst owner)

noncomputable def transferToKeyMem (dst owner : UInt256) : ByteArray :=
  wordAt32Mem dst (transferSenderHashMemAgain dst owner)

noncomputable def transferToHashMem (dst owner : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (transferToKeyMem dst owner)

noncomputable def transferLogMem (dst owner val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (transferToHashMem dst owner) 96 32

noncomputable def transferReturnMem (dst owner val : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (transferLogMem dst owner val) 96 32

theorem transferToArgMem_size (dst : UInt256) :
    (transferToArgMem dst).size = 96 := by
  unfold transferToArgMem
  rw [toByteArray_write_eq _ _ _ (by rw [transferDispatchMem_size]; omega)
      (by rw [transferDispatchMem_size]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, transferDispatchMem_size, ByteArray_zeroes_size,
    toByteArray_size]

theorem transferSenderKeyMem_size (dst owner : UInt256) :
    (transferSenderKeyMem dst owner).size = 96 := by
  unfold transferSenderKeyMem
  exact wordAt32Mem_size_96 owner (transferToArgMem_size dst)

theorem transferSenderHashMem_size (dst owner : UInt256) :
    (transferSenderHashMem dst owner).size = 96 := by
  unfold transferSenderHashMem
  exact wordAt0Mem_size_96 ⟨0⟩ (transferSenderKeyMem_size dst owner)

theorem transferSenderKeyMemAgain_size (dst owner : UInt256) :
    (transferSenderKeyMemAgain dst owner).size = 96 := by
  unfold transferSenderKeyMemAgain
  exact wordAt32Mem_size_96 owner (transferSenderHashMem_size dst owner)

theorem transferSenderHashMemAgain_size (dst owner : UInt256) :
    (transferSenderHashMemAgain dst owner).size = 96 := by
  unfold transferSenderHashMemAgain
  exact wordAt0Mem_size_96 ⟨0⟩ (transferSenderKeyMemAgain_size dst owner)

theorem transferToKeyMem_size (dst owner : UInt256) :
    (transferToKeyMem dst owner).size = 96 := by
  unfold transferToKeyMem
  exact wordAt32Mem_size_96 dst (transferSenderHashMemAgain_size dst owner)

theorem transferToHashMem_size (dst owner : UInt256) :
    (transferToHashMem dst owner).size = 96 := by
  unfold transferToHashMem
  exact wordAt0Mem_size_96 ⟨0⟩ (transferToKeyMem_size dst owner)

theorem transferLogMem_size (dst owner val : UInt256) :
    (transferLogMem dst owner val).size = 128 := by
  unfold transferLogMem
  simpa [transferToHashMem_size] using
    write_end_size_from (UInt256.toByteArray val) (transferToHashMem dst owner) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem transferToArgMem_read64 (dst : UInt256) :
    (transferToArgMem dst).readWithPadding 64 32 = UInt256.toByteArray dst := by
  unfold transferToArgMem
  exact toByteArray_write_read_back_of_gap dst transferDispatchMem 64
    (by rw [transferDispatchMem_size]; exact lt_usize 32 (by norm_num))

theorem transferSenderKeyMem_read32 (dst owner : UInt256) :
    (transferSenderKeyMem dst owner).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold transferSenderKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferToArgMem_size dst]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem transferSenderHashMem_read0 (dst owner : UInt256) :
    (transferSenderHashMem dst owner).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferSenderHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (transferSenderKeyMem dst owner)

theorem transferSenderHashMem_read32 (dst owner : UInt256) :
    (transferSenderHashMem dst owner).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold transferSenderHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferSenderKeyMem_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderKeyMem_size dst owner]; omega)]
  exact transferSenderKeyMem_read32 dst owner

theorem transferSenderHashMem_read64 (dst owner : UInt256) :
    (transferSenderHashMem dst owner).readWithPadding 64 32 = UInt256.toByteArray dst := by
  unfold transferSenderHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferSenderKeyMem_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderKeyMem_size dst owner])]
  unfold transferSenderKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferToArgMem_size dst]; omega)
    (by omega)
    (by rw [transferToArgMem_size dst])]
  exact transferToArgMem_read64 dst

theorem transferSenderKeyMemAgain_read64 (dst owner : UInt256) :
    (transferSenderKeyMemAgain dst owner).readWithPadding 64 32 = UInt256.toByteArray dst := by
  unfold transferSenderKeyMemAgain wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferSenderHashMem_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderHashMem_size dst owner])]
  exact transferSenderHashMem_read64 dst owner

theorem transferSenderHashMemAgain_read0 (dst owner : UInt256) :
    (transferSenderHashMemAgain dst owner).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferSenderHashMemAgain
  exact wordAt0Mem_read0 ⟨0⟩ (transferSenderKeyMemAgain dst owner)

theorem transferSenderHashMemAgain_read32 (dst owner : UInt256) :
    (transferSenderHashMemAgain dst owner).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold transferSenderHashMemAgain wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferSenderKeyMemAgain_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderKeyMemAgain_size dst owner]; omega)]
  unfold transferSenderKeyMemAgain wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferSenderHashMem_size dst owner]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem transferSenderHashMemAgain_read64 (dst owner : UInt256) :
    (transferSenderHashMemAgain dst owner).readWithPadding 64 32 = UInt256.toByteArray dst := by
  unfold transferSenderHashMemAgain wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferSenderKeyMemAgain_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderKeyMemAgain_size dst owner])]
  exact transferSenderKeyMemAgain_read64 dst owner

theorem transferSenderHashMem_read0_64 (dst owner : UInt256) :
    (transferSenderHashMem dst owner).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray owner := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferSenderHashMem_size dst owner]; omega)]
  have hleft :
      (transferSenderHashMem dst owner).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferSenderHashMem_size dst owner]; omega),
      transferSenderHashMem_read0 dst owner]
  have hright :
      (transferSenderHashMem dst owner).extract 32 64 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferSenderHashMem_size dst owner]; omega),
      transferSenderHashMem_read32 dst owner]
  rw [show (transferSenderHashMem dst owner).extract 0 64 =
      (transferSenderHashMem dst owner).extract 0 32 ++
        (transferSenderHashMem dst owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferSenderHashMemAgain_read0_64 (dst owner : UInt256) :
    (transferSenderHashMemAgain dst owner).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray owner := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferSenderHashMemAgain_size dst owner]; omega)]
  have hleft :
      (transferSenderHashMemAgain dst owner).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferSenderHashMemAgain_size dst owner]; omega),
      transferSenderHashMemAgain_read0 dst owner]
  have hright :
      (transferSenderHashMemAgain dst owner).extract 32 64 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferSenderHashMemAgain_size dst owner]; omega),
      transferSenderHashMemAgain_read32 dst owner]
  rw [show (transferSenderHashMemAgain dst owner).extract 0 64 =
      (transferSenderHashMemAgain dst owner).extract 0 32 ++
        (transferSenderHashMemAgain dst owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferSenderKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferSenderHashMem (transferToWord I) (approveOwnerWord I))
          |>.readWithPadding 0 64)))
      = transferSenderSlotI I := by
  rw [transferSenderHashMem_read0_64]
  unfold transferSenderSlotI erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address]
  unfold approveOwnerWord
  exact keccakSlot_eq _

theorem transferSenderKeccakSlotAgain (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
          |>.readWithPadding 0 64)))
      = transferSenderSlotI I := by
  rw [transferSenderHashMemAgain_read0_64]
  unfold transferSenderSlotI erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address]
  unfold approveOwnerWord
  exact keccakSlot_eq _

theorem transferToKeyMem_read32 (dst owner : UInt256) :
    (transferToKeyMem dst owner).readWithPadding 32 32 = UInt256.toByteArray dst := by
  unfold transferToKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferSenderHashMemAgain_size dst owner]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray dst).size ≤ 32
    rw [toByteArray_size])

theorem transferToHashMem_read0 (dst owner : UInt256) :
    (transferToHashMem dst owner).readWithPadding 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold transferToHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (transferToKeyMem dst owner)

theorem transferToHashMem_read32 (dst owner : UInt256) :
    (transferToHashMem dst owner).readWithPadding 32 32 = UInt256.toByteArray dst := by
  unfold transferToHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [transferToKeyMem_size dst owner]; omega)
    (by omega)
    (by rw [transferToKeyMem_size dst owner]; omega)]
  exact transferToKeyMem_read32 dst owner

theorem transferToHashMem_read64 (dst owner : UInt256) :
    (transferToHashMem dst owner).readWithPadding 64 32 = UInt256.toByteArray dst := by
  unfold transferToHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [transferToKeyMem_size dst owner]; omega)
    (by omega)
    (by rw [transferToKeyMem_size dst owner])]
  unfold transferToKeyMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [transferSenderHashMemAgain_size dst owner]; omega)
    (by omega)
    (by rw [transferSenderHashMemAgain_size dst owner])]
  exact transferSenderHashMemAgain_read64 dst owner

theorem transferToHashMem_read0_64 (dst owner : UInt256) :
    (transferToHashMem dst owner).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray dst := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [transferToHashMem_size dst owner]; omega)]
  have hleft :
      (transferToHashMem dst owner).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [transferToHashMem_size dst owner]; omega),
      transferToHashMem_read0 dst owner]
  have hright :
      (transferToHashMem dst owner).extract 32 64 = UInt256.toByteArray dst := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [transferToHashMem_size dst owner]; omega),
      transferToHashMem_read32 dst owner]
  rw [show (transferToHashMem dst owner).extract 0 64 =
      (transferToHashMem dst owner).extract 0 32 ++
        (transferToHashMem dst owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem transferToKeccakSlot (I : ExecutionEnv)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((transferToHashMem (transferToWord I) (approveOwnerWord I))
          |>.readWithPadding 0 64)))
      = transferToSlot I := by
  rw [transferToHashMem_read0_64]
  unfold transferToSlot erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanonTo]
  exact keccakSlot_eq _

theorem transferLogMem_read96 (dst owner val : UInt256) :
    (transferLogMem dst owner val).readWithPadding 96 32 = UInt256.toByteArray val := by
  unfold transferLogMem
  exact toByteArray_write_read_back_of_gap val (transferToHashMem dst owner) 96
    (by rw [transferToHashMem_size]; exact lt_usize 0 (by norm_num))

theorem transferReturnMem_read96 (dst owner val : UInt256) :
    (transferReturnMem dst owner val).readWithPadding 96 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold transferReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [transferLogMem_size dst owner val]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem transferDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ transferDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (transferDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨24⟩ : UInt256) := by
  native_decide

theorem transferFromBalanceWord_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (transferSenderSlotI I) =
      transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) := by
  simp [transferFromBalanceWord, transferSenderSlot, transferSenderSlotI, initState]

theorem transferToBalanceWord_afterSenderStore_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
          (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        I.codeOwner (transferToSlot I) =
      transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
  simp [transferToBalanceWord, transferAfterDebitState, transferSenderSlot, transferSenderSlotI,
    initState]

def transferSenderBalanceRaw (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferSenderSlotI I) ⟨0⟩)
    (Batteries.RBMap.find? σ I.codeOwner)

def transferToBalanceRawAfterDebit (σ : AccountMap) (I : ExecutionEnv) (debit : UInt256) :
    UInt256 :=
  Option.option (⟨0⟩ : UInt256)
    (fun ac => Batteries.RBMap.findD ac.storage (transferToSlot I) ⟨0⟩)
    (Batteries.RBMap.find?
      (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I) debit) I.codeOwner)

theorem transferSenderBalanceRaw_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferSenderBalanceRaw σ I =
      transferFromBalanceWord (initState cA gh bl σ σ₀ g A I) := by
  simpa [transferSenderBalanceRaw, transferFromBalanceWord, transferSenderSlot,
    transferSenderSlotI, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage] using
    (transferFromBalanceWord_initState (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))

theorem transferToBalanceRawAfterDebit_initState {cA gh bl σ σ₀ A I} {g : Sat256} :
    transferToBalanceRawAfterDebit σ I
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I) =
      transferToBalanceWord (initState cA gh bl σ σ₀ g A I) I := by
  simpa [transferToBalanceRawAfterDebit, transferToBalanceWord_afterSenderStore_initState,
    Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    vyperERC20StorageStore_accountMap]
    using (transferToBalanceWord_afterSenderStore_initState
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))

macro "vyper_erc20_transfer_decode" : tactic =>
  `(tactic| native_decide)

theorem transferRevertStub {cA gh bl σ σ₀ A I} {g : Sat256}
    {pc stk mem aw rdata acc k C}
    (hreach : RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) pc
      stk mem aw rdata acc k C)
    (hpc : pc = ⟨801⟩)
    (hov : stk.length + 2 ≤ 1024) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  subst pc
  have rd804 := evm_run hreach with [
    jumpdest,
    push0,
    dup1]
  exact rd804.rev 0 (by vyper_erc20_transfer_decode)
    (fun s _ hstks => memExpRevert0 s hstks) (by omega)

theorem calldataSizeGuard68_short {n : Nat}
    (hsize : n < UInt256.size) (hshort : n < 68) :
    UInt256.lt (UInt256.ofNat n) ⟨68⟩ = ⟨1⟩ := by
  exact ult_one (by
    have hn : (UInt256.ofNat n).toNat = n := by
      unfold UInt256.toNat UInt256.ofNat
      simp only [Id.run]
      exact Nat.mod_eq_of_lt hsize
    rw [hn]
    change n < 68
    exact hshort)

theorem erc20X_transferAfterBalanceGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨80⟩
      [transferSelectorWord]
      (transferSenderHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd24⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hslotFrom := transferSenderKeccakSlot I
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonToGuard : UInt256.shiftRight (transferToWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (transferToWord I) hcanonTo
  have hbalanceGuard :
      UInt256.lt (transferFromBalanceWord evm0) (transferValueWord I) = ⟨0⟩ := by
    exact ult_zero (by simpa [evm0] using henough)
  have hbalanceGuardRaw :
      UInt256.lt
        (Option.option (⟨0⟩ : UInt256)
          (fun ac => Batteries.RBMap.findD ac.storage (transferSenderSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner))
        (transferValueWord I) = ⟨0⟩ := by
    simpa [evm0, transferFromBalanceWord, transferSenderSlot, transferSenderSlotI,
      initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using hbalanceGuard
  have rdBeforeSenderLoad := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by native_decide),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [transferToWord, calldataWord] using hcanonToGuard),
    push1 ⟨64⟩,
    raw mstore 6 (transferToArgMem (transferToWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨36⟩, calldataload,
    push0, caller, push1 ⟨32⟩,
    raw mstore 0 (transferSenderKeyMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0 (transferSenderHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferSenderSlotI I)
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost hslotFrom (by decide) (by evm_ov)]
  obtain ⟨k1, C1, rdAfterSenderLoad⟩ := rdBeforeSenderLoad.sload
    (by vyper_erc20_transfer_decode) (by evm_ov)
  have rdAfterBalanceGuard := evm_run rdAfterSenderLoad with [
    lt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferValueWord] using hbalanceGuardRaw)]
  exact ⟨_, _, by simpa [evm0] using rdAfterBalanceGuard⟩

theorem erc20X_transferBeforeSecondSenderLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨80⟩
      [transferSelectorWord]
      (transferSenderHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨92⟩
      [transferSenderSlotI I, transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd80⟩ := hreach
  have hslotFrom := transferSenderKeccakSlotAgain I
  have rdBeforeSenderStore := evm_run rd80 with [
    push0, caller, push1 ⟨32⟩,
    raw mstore 0 (transferSenderKeyMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by unfold transferSenderKeyMemAgain wordAt32Mem approveOwnerWord; rfl)
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by unfold transferSenderHashMemAgain wordAt0Mem; rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferSenderSlotI I)
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost hslotFrom (by decide) (by evm_ov),
    dup1]
  exact ⟨_, _, rdBeforeSenderStore⟩

theorem erc20X_transferAfterSecondSenderLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨92⟩
      [transferSenderSlotI I, transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨93⟩
      [transferSenderBalanceRaw σ I, transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd92⟩ := hreach
  obtain ⟨k1, C1, rdAfterSenderLoad⟩ := rd92.sload
    (by vyper_erc20_transfer_decode) (by evm_ov)
  exact ⟨_, _, by simpa [transferSenderBalanceRaw] using rdAfterSenderLoad⟩

theorem erc20X_transferBeforeSenderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨93⟩
      [transferSenderBalanceRaw σ I, transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨111⟩
      [transferSenderSlotI I,
        transferDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd93⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hsenderLoadRaw :
      transferSenderBalanceRaw σ I = transferFromBalanceWord evm0 := by
    simpa [evm0] using
      (transferSenderBalanceRaw_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hsenderEnoughRaw :
      (transferValueWord I).toNat ≤ (transferSenderBalanceRaw σ I).toNat := by
    rw [hsenderLoadRaw]
    simpa [evm0] using henough
  have hdebitNat :
      (transferDebitWord evm0 I).toNat =
        (transferFromBalanceWord evm0).toNat - (transferValueWord I).toNat := by
    unfold transferDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) (transferFromBalanceWord evm0).val.isLt)
  have hdebitWordRaw :
      UInt256.sub (transferSenderBalanceRaw σ I) (transferValueWord I) =
        transferDebitWord evm0 I := by
    apply u256_inj
    rw [usub_toNat hsenderEnoughRaw, hsenderLoadRaw, hdebitNat]
  have hdebitGuardRaw :
      UInt256.gt
          (UInt256.sub (transferSenderBalanceRaw σ I) (transferValueWord I))
          (transferSenderBalanceRaw σ I) = ⟨0⟩ := by
    exact ugt_zero (by
      rw [usub_toNat hsenderEnoughRaw]
      exact Nat.sub_le _ _)
  have rdBeforeSenderStore := evm_run rd93 with [
    push1 ⟨36⟩, calldataload,
    dup1, dup3, sub, dup3, dup2, gt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferValueWord] using hdebitGuardRaw),
    swap1, pop, swap1, pop, dup2]
  have hdebitWordRaw' :
      UInt256.sub (transferSenderBalanceRaw σ I)
          (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32)) =
        transferDebitWord evm0 I := by
    simpa [transferValueWord] using hdebitWordRaw
  have hpc111 :
      (⟨93⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                  ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                ⟨1⟩ + ⟨1⟩ =
        (⟨111⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [evm0, hdebitWordRaw', hpc111] using rdBeforeSenderStore⟩

theorem erc20X_transferAfterSenderStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨111⟩
      [transferSenderSlotI I,
        transferDebitWord (initState cA gh bl σ σ₀ g A I) I,
        transferSenderSlotI I, transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd111⟩ := hreach
  obtain ⟨k1, C1, rdAfterStore⟩ :=
    rd111.sstore hperm (by vyper_erc20_transfer_decode) (by evm_ov)
  exact ⟨_, _, evm_run rdAfterStore with [pop]⟩

theorem erc20X_transferBeforeToLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [transferSelectorWord]
      (transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨127⟩
      [transferToSlot I, transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd113⟩ := hreach
  have hslotTo := transferToKeccakSlot I hcanonTo
  have rdBeforeToLoad := evm_run rd113 with [
    push0, push1 ⟨64⟩,
    raw mload 0 (transferToWord I) (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferSenderHashMemAgain (transferToWord I) (approveOwnerWord I))
          (aw := UInt256.ofNat 3) (off := ⟨64⟩) (v := transferToWord I)
          (by rw [transferSenderHashMemAgain_size]; decide)
          (by decide)
          (transferSenderHashMemAgain_read64 (transferToWord I) (approveOwnerWord I)))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (transferToKeyMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by unfold transferToKeyMem wordAt32Mem; rfl)
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by unfold transferToHashMem wordAt0Mem; rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferToSlot I)
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost hslotTo (by decide) (by evm_ov),
    dup1]
  exact ⟨_, _, rdBeforeToLoad⟩

theorem erc20X_transferAfterToLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨127⟩
      [transferToSlot I, transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨128⟩
      [transferToBalanceRawAfterDebit σ I
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I),
        transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd127⟩ := hreach
  obtain ⟨k1, C1, rdAfterToLoad⟩ := rd127.sload
    (by vyper_erc20_transfer_decode) (by evm_ov)
  exact ⟨_, _, by simpa [transferToBalanceRawAfterDebit] using rdAfterToLoad⟩

theorem erc20X_transferBeforeToStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨128⟩
      [transferToBalanceRawAfterDebit σ I
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I),
        transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨146⟩
      [transferToSlot I,
        transferNewToWord (initState cA gh bl σ σ₀ g A I) I,
        transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd128⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  let debit := transferDebitWord evm0 I
  have htoLoadRaw :
      transferToBalanceRawAfterDebit σ I debit = transferToBalanceWord evm0 I := by
    simpa [evm0, debit] using
      (transferToBalanceRawAfterDebit_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hnewRaw :
      transferToBalanceRawAfterDebit σ I debit + transferValueWord I =
        transferNewToWord evm0 I := by
    apply u256_inj
    rw [uadd_toNat, Nat.mod_eq_of_lt (by
      rw [htoLoadRaw]
      simpa [evm0, transferNewToNat] using hfit)]
    rw [transferNewToWord_toNat evm0 I hfit, transferNewToNat, htoLoadRaw]
  have hcreditGuardRaw :
      UInt256.lt
          (transferToBalanceRawAfterDebit σ I debit + transferValueWord I)
          (transferToBalanceRawAfterDebit σ I debit) = ⟨0⟩ := by
    exact ult_zero (by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by
        rw [htoLoadRaw]
        simpa [evm0, transferNewToNat] using hfit), htoLoadRaw]
      rw [transferNewToNat] at hfit
      exact Nat.le_add_right _ _)
  have rdBeforeToStore := evm_run rd128 with [
    push1 ⟨36⟩, calldataload,
    dup1, dup3, add, dup3, dup2, lt, push2 ⟨801⟩,
    jumpiNT (by simpa [transferValueWord] using hcreditGuardRaw),
    swap1, pop, swap1, pop, dup2]
  have hnewRaw' :
      transferToBalanceRawAfterDebit σ I debit +
          uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) =
        transferNewToWord evm0 I := by
    simpa [transferValueWord] using hnewRaw
  have hpc146 :
      (⟨128⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                  ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
                ⟨1⟩ + ⟨1⟩ =
        (⟨146⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [evm0, debit, hnewRaw', hpc146] using rdBeforeToStore⟩

theorem erc20X_transferAfterToStore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨146⟩
      [transferToSlot I,
        transferNewToWord (initState cA gh bl σ σ₀ g A I) I,
        transferToSlot I, transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
        (transferDebitWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨148⟩
      [transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd146⟩ := hreach
  obtain ⟨k1, C1, rdAfterStore⟩ :=
    rd146.sstore hperm (by vyper_erc20_transfer_decode) (by evm_ov)
  exact ⟨_, _, evm_run rdAfterStore with [pop]⟩

theorem erc20X_transferBeforeLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨148⟩
      [transferSelectorWord]
      (transferToHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨195⟩
      [⟨96⟩, ⟨32⟩, transferEventTopic, approveOwnerWord I, transferToWord I,
        transferSelectorWord]
      (transferLogMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd148⟩ := hreach
  have rdAfterTopic := (evm_run rd148 with [
    push1 ⟨64⟩,
    raw mload 0 (transferToWord I) (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := transferToHashMem (transferToWord I) (approveOwnerWord I))
          (aw := UInt256.ofNat 3) (off := ⟨64⟩) (v := transferToWord I)
          (by rw [transferToHashMem_size]; decide)
          (by decide)
          (transferToHashMem_read64 (transferToWord I) (approveOwnerWord I)))
      (by decide) (by evm_ov),
    caller]).pushConst transferEventTopic (width := 32) (op := .PUSH32)
      (by decide) (by vyper_erc20_transfer_decode) (by evm_ov)
  have rdBeforeLog := evm_run rdAfterTopic with [
    push1 ⟨36⟩, calldataload,
    push1 ⟨96⟩,
    raw mstore 3 (transferLogMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨96⟩]
  have hpc195 :
      (⟨148⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 33 +
                  UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
                UInt256.ofNat 2 =
        (⟨195⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by simpa [approveOwnerWord, transferValueWord, hpc195] using rdBeforeLog⟩

theorem erc20X_transferAfterLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨195⟩
      [⟨96⟩, ⟨32⟩, transferEventTopic, approveOwnerWord I, transferToWord I,
        transferSelectorWord]
      (transferLogMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩
      [transferSelectorWord]
      (transferLogMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C := by
  obtain ⟨k, C, rd195⟩ := hreach
  exact ⟨_, _, rd195.log3 0 (UInt256.ofNat 4)
    (by vyper_erc20_transfer_decode) hperm mem_cost (by decide) (by evm_ov)⟩

theorem erc20X_transferReturnFromAfterLog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨196⟩
      [transferSelectorWord]
      (transferLogMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I)) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨k, C, rd196⟩ := hreach
  have rdBeforeReturn := evm_run rd196 with [
    push1 ⟨1⟩, push1 ⟨96⟩,
    raw mstore 0 (transferReturnMem (transferToWord I) (approveOwnerWord I) (transferValueWord I))
      (UInt256.ofNat 4)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨96⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256))
    (by vyper_erc20_transfer_decode)
    mem_cost
    (transferReturnMem_read96 (transferToWord I) (approveOwnerWord I) (transferValueWord I))
    (by evm_ov)

theorem erc20X_transferFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hfit : transferNewToNat (initState cA gh bl σ σ₀ g A I) I < UInt256.size)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ (transferSenderSlotI I)
          (transferDebitWord (initState cA gh bl σ σ₀ g A I) I))
        (transferToSlot I) (transferNewToWord (initState cA gh bl σ σ₀ g A I) I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  have h80 := erc20X_transferAfterBalanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz68 hsize hcanonTo henough hreach
  have h92 := erc20X_transferBeforeSecondSenderLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h80
  have h93 := erc20X_transferAfterSecondSenderLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h92
  have h111 := erc20X_transferBeforeSenderStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    henough h93
  have h113 := erc20X_transferAfterSenderStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h111
  have h127 := erc20X_transferBeforeToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonTo h113
  have h128 := erc20X_transferAfterToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h127
  have h146 := erc20X_transferBeforeToStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hfit h128
  have h148 := erc20X_transferAfterToStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h146
  have h195 := erc20X_transferBeforeLog
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h148
  have h196 := erc20X_transferAfterLog
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h195
  exact erc20X_transferReturnFromAfterLog
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h196

theorem erc20TransferX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd24⟩ := hreach
  have hsizeGuard := calldataSizeGuard68_short (n := I.calldata.size) hsize hshort
  have rd801 := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by native_decide),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiT (by rw [hsizeGuard, hwv]; decide) (by vyper_erc20_transfer_decode)]
  exact transferRevertStub (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by norm_num)

theorem erc20TransferX_noncanon_to {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (transferToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd24⟩ := hreach
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonToGuard : UInt256.shiftRight (transferToWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (transferToWord I) hzero)
  have rd801 := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by native_decide),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiT (by
      simp [transferToWord, calldataWord]
      exact hcanonToGuard) (by vyper_erc20_transfer_decode)]
  exact transferRevertStub (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20TransferX_insufficient {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (hlt : (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat <
      (transferValueWord I).toNat)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd24⟩ := hreach
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hslotFrom := transferSenderKeccakSlot I
  have hsizeGuard := calldataSizeGuard68 (n := I.calldata.size) hsz68 hsize
  have hcanonToGuard : UInt256.shiftRight (transferToWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (transferToWord I) hcanonTo
  have hbalanceGuard :
      UInt256.lt (transferFromBalanceWord evm0) (transferValueWord I) = ⟨1⟩ := by
    exact ult_one (by simpa [evm0] using hlt)
  have hbalanceGuardRaw :
      UInt256.lt
        (Option.option (⟨0⟩ : UInt256)
          (fun ac => Batteries.RBMap.findD ac.storage (transferSenderSlotI I) ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner))
        (transferValueWord I) = ⟨1⟩ := by
    simpa [evm0, transferFromBalanceWord, transferSenderSlot, transferSenderSlotI,
      initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using hbalanceGuard
  have rdBeforeSenderLoad := evm_run rd24 with [
    jumpdest,
    raw push4 transferSelectorWord (by vyper_erc20_transfer_decode) (by evm_ov),
    dup2, xor, push2 ⟨797⟩, jumpiNT (by native_decide),
    push1 ⟨68⟩, calldatasize, lt, callvalue, or, push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩, calldataload, dup1, push1 ⟨160⟩, shr, push2 ⟨801⟩,
    jumpiNT (by simpa [transferToWord, calldataWord] using hcanonToGuard),
    push1 ⟨64⟩,
    raw mstore 6 (transferToArgMem (transferToWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨36⟩, calldataload,
    push0, caller, push1 ⟨32⟩,
    raw mstore 0 (transferSenderKeyMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push0,
    raw mstore 0 (transferSenderHashMem (transferToWord I) (approveOwnerWord I))
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (transferSenderSlotI I)
      (UInt256.ofNat 3)
      (by vyper_erc20_transfer_decode) mem_cost hslotFrom (by decide) (by evm_ov)]
  obtain ⟨k1, C1, rdAfterSenderLoad⟩ := rdBeforeSenderLoad.sload
    (by vyper_erc20_transfer_decode) (by evm_ov)
  have rd801 := evm_run rdAfterSenderLoad with [
    lt, push2 ⟨801⟩,
    jumpiT (by rw [show
        UInt256.lt
          (Option.option (⟨0⟩ : UInt256)
            (fun ac => Batteries.RBMap.findD ac.storage (transferSenderSlotI I) ⟨0⟩)
            (Batteries.RBMap.find? σ I.codeOwner))
          (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32)) =
          ⟨1⟩ by simpa [transferValueWord] using hbalanceGuardRaw]; decide)
      (by vyper_erc20_transfer_decode)]
  exact transferRevertStub (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20TransferX_overflow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanonTo : (transferToWord I).toNat < EVM.addressModulus)
    (henough : (transferValueWord I).toNat ≤
      (transferFromBalanceWord (initState cA gh bl σ σ₀ g A I)).toNat)
    (hover : UInt256.size ≤ transferNewToNat (initState cA gh bl σ σ₀ g A I) I)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  let debit := transferDebitWord evm0 I
  have h80 := erc20X_transferAfterBalanceGuard
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hwv hsz68 hsize hcanonTo henough hreach
  have h92 := erc20X_transferBeforeSecondSenderLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h80
  have h93 := erc20X_transferAfterSecondSenderLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h92
  have h111 := erc20X_transferBeforeSenderStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    henough h93
  have h113 := erc20X_transferAfterSenderStore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hperm h111
  have h127 := erc20X_transferBeforeToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcanonTo h113
  have h128 := erc20X_transferAfterToLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) h127
  obtain ⟨k, C, rd128⟩ := h128
  have htoLoadRaw :
      transferToBalanceRawAfterDebit σ I debit = transferToBalanceWord evm0 I := by
    simpa [evm0, debit] using
      (transferToBalanceRawAfterDebit_initState (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
  have hoverRaw :
      UInt256.size ≤
        (transferToBalanceRawAfterDebit σ I debit).toNat + (transferValueWord I).toNat := by
    rw [htoLoadRaw]
    simpa [evm0, transferNewToNat] using hover
  have hcreditGuardRaw :
      UInt256.lt
          (transferToBalanceRawAfterDebit σ I debit + transferValueWord I)
          (transferToBalanceRawAfterDebit σ I debit) = ⟨1⟩ := by
    simpa [u256_add_comm] using
      constructorCheckedAddOverflowLt
        (transferToBalanceRawAfterDebit σ I debit) (transferValueWord I) hoverRaw
  have rd801 := evm_run rd128 with [
    push1 ⟨36⟩, calldataload,
    dup1, dup3, add, dup3, dup2, lt, push2 ⟨801⟩,
    jumpiT (by rw [show
        UInt256.lt
          (transferToBalanceRawAfterDebit σ I debit +
            uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
          (transferToBalanceRawAfterDebit σ I debit) = ⟨1⟩ by
          simpa [transferValueWord] using hcreditGuardRaw]; decide)
      (by vyper_erc20_transfer_decode)]
  exact transferRevertStub (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by
      simp only [List.length_cons, List.length_nil]
      omega)

theorem erc20TransferSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem transferSelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      transferSelectorWord := by
  have h := evmSelectorDecode hsz 0xa9 0x05 0x9c 0xbb transferSelectorWord (by native_decide)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      transferSelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem erc20X_transferReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz := erc20TransferSelector_size hsel
  have hword := transferSelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0, calldataload, push1 ⟨224⟩, shr, push1 ⟨2⟩, push1 ⟨7⟩, dup3, mod,
    push1 ⟨1⟩, shl, push2 ⟨805⟩, add, push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, transferSelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 transferDispatchMem (UInt256.ofNat 1)
    (by vyper_erc20_transfer_decode) mem_cost (by native_decide) (by decide) (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨24⟩ (UInt256.ofNat 1)
      (by vyper_erc20_transfer_decode)
      mem_cost
      transferDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_transfer_decode) (by native_decide) (by evm_ov)⟩

theorem erc20Dispatch_transfer {cd : ByteArray}
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.transferTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [ERC20.approveTransition, ERC20.totalSupplyTransition,
      ERC20.transferFromTransition, ERC20.balanceOfTransition])
    (post := [ERC20.allowanceTransition])
    rfl rfl ?_ (by rw [selectorOf, vyperERC20TransferSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, vyperERC20TotalSupplySelectorBytes, hcd]; decide
  · rw [selectorOf, vyperERC20TransferFromSelectorBytes, hcd]; decide
  · rw [selectorOf, vyperERC20BalanceOfSelectorBytes, hcd]; decide

theorem erc20TransferBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨24⟩
      [transferSelectorWord] transferDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc20TransferSelector_size hsel
  have hd := erc20Dispatch_transfer (cd := I.calldata) hsel
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσ : EVMStateEquiv evmE evmS := by
    simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
  have hFromBalance : transferFromBalanceWord evmE = transferFromBalanceWord evmS := by
    unfold transferFromBalanceWord transferSenderSlot
    rw [hσ.executionEnv]
    exact hσ.storageLoad_codeOwner (erc20BalanceOfSlot (.address evmS.executionEnv.source))
  have hDebit : transferDebitWord evmE I = transferDebitWord evmS I := by
    simp [transferDebitWord, hFromBalance]
  have hσDebit : EVMStateEquiv (transferAfterDebitState evmE I)
      (transferAfterDebitState evmS I) := by
    unfold transferAfterDebitState transferSenderSlot
    rw [hσ.executionEnv, hDebit]
    exact hσ.storageStore_codeOwner
      (erc20BalanceOfSlot (.address evmS.executionEnv.source)) rfl
  have hToBalance : transferToBalanceWord evmE I = transferToBalanceWord evmS I := by
    unfold transferToBalanceWord
    exact hσDebit.storageLoad (congrArg ExecutionEnv.codeOwner hσ.executionEnv) (transferToSlot I)
  have hNewToNat : transferNewToNat evmE I = transferNewToNat evmS I := by
    simp [transferNewToNat, hToBalance]
  have hNewToWord : transferNewToWord evmE I = transferNewToWord evmS I := by
    simp [transferNewToWord, hNewToNat]
  have hσPost : EVMStateEquiv (transferPostState evmE I) (transferPostState evmS I) := by
    unfold transferPostState
    rw [hσ.executionEnv, hNewToWord]
    exact hσDebit.storageStore (congrArg ExecutionEnv.codeOwner hσ.executionEnv)
      (transferToSlot I) rfl
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hcanonTo : (transferToWord I).toNat < EVM.addressModulus
    · have hdec0 := erc20Decode_transfer_ok (I := I) hsz68 hcanonTo
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.transferTransition.params.map Param.name)
            (transitionSignature ERC20.transferTransition).paramTypes I.calldata =
              some (transferStore I) := by
        simpa [vyperERC20Config] using hdec0
      by_cases henough : (transferValueWord I).toNat ≤
          (transferFromBalanceWord evmE).toNat
      · by_cases hfit : transferNewToNat evmE I < UInt256.size
        · have henoughS : (transferValueWord I).toNat ≤ (transferFromBalanceWord evmS).toNat := by
            simpa [hFromBalance] using henough
          have hbody := erc20TransferBodyReturns evmS I
            (by simp only [evmS, initState]; exact hwv) henoughS
            (by simpa [hNewToNat] using hfit)
          exact (erc20X_transferFromEntry (g := Sat256.ofUInt256 g)
              hwv hperm hsz68 hsize hcanonTo
              (by simpa [evmE] using henough)
              (by simpa [evmE] using hfit) hreach)
            |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
              (by simp [evmE, initState, transferPostState, transferAfterDebitState,
                transferSenderSlot, transferSenderSlotI, vyperERC20StorageStore_createdAccounts])
              (accountMapEquiv.of_eq (by
                simp [evmE, initState, transferPostState, transferAfterDebitState,
                  transferSenderSlot, transferSenderSlotI, vyperERC20StorageStore_accountMap]))
              hσPost
              (returnEquiv_of_encode ERC20.erc20BoolTrueReturnEncoding)
        · have hover : UInt256.size ≤ transferNewToNat evmE I := by omega
          have henoughS : (transferValueWord I).toNat ≤ (transferFromBalanceWord evmS).toNat := by
            simpa [hFromBalance] using henough
          have hbody := erc20TransferBodyReverts_overflow evmS I
            (by simp only [evmS, initState]; exact hwv) henoughS
            (by simpa [hNewToNat] using hover)
          exact (erc20TransferX_overflow (g := Sat256.ofUInt256 g)
              hwv hperm hsz68 hsize hcanonTo
              (by simpa [evmE] using henough)
              (by simpa [evmE] using hover) hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hlt : (transferFromBalanceWord evmE).toNat < (transferValueWord I).toNat := by
          omega
        have hltS : (transferFromBalanceWord evmS).toNat < (transferValueWord I).toNat := by
          simpa [hFromBalance] using hlt
        have hbody := erc20TransferBodyReverts_insufficient evmS I
          (by simp only [evmS, initState]; exact hwv) hltS
        exact (erc20TransferX_insufficient (g := Sat256.ofUInt256 g)
            hwv hsz68 hsize hcanonTo (by simpa [evmE] using hlt) hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hdec0 := erc20Decode_transfer_none_noncanon (I := I) hsz68 hcanonTo
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.transferTransition.params.map Param.name)
            (transitionSignature ERC20.transferTransition).paramTypes I.calldata = none := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20TransferX_noncanon_to (g := Sat256.ofUInt256 g)
          hwv hsz68 hsize hcanonTo hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec0 := erc20Decode_transfer_none_short (I := I) hsz4 hshort
    have hdec :
        decodeCalldataWithMode vyperERC20Config.abiDecodeMode
          (ERC20.transferTransition.params.map Param.name)
          (transitionSignature ERC20.transferTransition).paramTypes I.calldata = none := by
      simpa [vyperERC20Config] using hdec0
    exact (erc20TransferX_shortarg (g := Sat256.ofUInt256 g) hwv hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem erc20TransferRuntimeSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20TransferBodyCore hcode hwv hperm hsize hsel
    (erc20X_transferReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

end VyperERC20
