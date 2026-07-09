import Examples.UniswapV2Pair.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

/-! # Shared `_burn` source helpers -/

abbrev burnFunctionFromValue (holder : AccountAddress) : Value :=
  .address holder

abbrev burnFunctionValueValue (value : UInt256) : Value :=
  uniswapUint256Value value

abbrev burnFunctionFromKey (holder : AccountAddress) : KeyValue :=
  .address holder

abbrev burnFunctionCallStore (holder : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "value" (burnFunctionValueValue value)).insert "from"
    (burnFunctionFromValue holder)

def burnFunctionFromSlot (holder : AccountAddress) : UInt256 :=
  balanceOfSlot (burnFunctionFromKey holder)

def burnFunctionFromBalanceWord (evm : EVM.State) (holder : AccountAddress) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (burnFunctionFromSlot holder)

abbrev burnFunctionFromBalanceValue (evm : EVM.State) (holder : AccountAddress) : Value :=
  uniswapUint256Value (burnFunctionFromBalanceWord evm holder)

def burnFunctionBalanceDebitWord (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) : UInt256 :=
  UInt256.ofNat ((burnFunctionFromBalanceWord evm holder).toNat - value.toNat)

abbrev burnFunctionBalanceDebitValue (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) : Value :=
  uniswapUint256Value (burnFunctionBalanceDebitWord evm holder value)

abbrev burnFunctionAfterBalanceStore
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : Store :=
  (burnFunctionCallStore holder value).insert "fromBalance"
    (burnFunctionFromBalanceValue evm holder)

def burnFunctionAfterBalanceState
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (burnFunctionFromSlot holder)
    (burnFunctionBalanceDebitWord evm holder value)

def burnFunctionTotalSupplyWord
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : UInt256 :=
  Solm.EVM.storageLoad (burnFunctionAfterBalanceState evm holder value)
    evm.executionEnv.codeOwner ⟨0⟩

abbrev burnFunctionTotalSupplyValue
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : Value :=
  uniswapUint256Value (burnFunctionTotalSupplyWord evm holder value)

abbrev burnFunctionAfterTotalSupplyStore
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : Store :=
  (burnFunctionAfterBalanceStore evm holder value).insert "_totalSupply"
    (burnFunctionTotalSupplyValue evm holder value)

def burnFunctionTotalSupplyDebitWord
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : UInt256 :=
  UInt256.ofNat ((burnFunctionTotalSupplyWord evm holder value).toNat - value.toNat)

abbrev burnFunctionTotalSupplyDebitValue
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : Value :=
  uniswapUint256Value (burnFunctionTotalSupplyDebitWord evm holder value)

def burnFunctionPostState
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore (burnFunctionAfterBalanceState evm holder value)
    evm.executionEnv.codeOwner ⟨0⟩ (burnFunctionTotalSupplyDebitWord evm holder value)

def burnFunctionFromEvaledRef (holder : AccountAddress) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (burnFunctionFromKey holder)] }

theorem burnFunctionCallStore_from (holder : AccountAddress) (value : UInt256) :
    (burnFunctionCallStore holder value).get? "from" =
      some (burnFunctionFromValue holder) := by
  rw [burnFunctionCallStore, store_get_self]

theorem burnFunctionCallStore_value (holder : AccountAddress) (value : UInt256) :
    (burnFunctionCallStore holder value).get? "value" =
      some (burnFunctionValueValue value) := by
  rw [burnFunctionCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem burnFunctionCallStore_balanceOf (holder : AccountAddress) (value : UInt256) :
    (burnFunctionCallStore holder value).get? "balanceOf" = none := by
  rw [burnFunctionCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem burnFunctionCallStore_totalSupply (holder : AccountAddress) (value : UInt256) :
    (burnFunctionCallStore holder value).get? "totalSupply" = none := by
  rw [burnFunctionCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem burnFunctionAfterBalanceStore_from (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    (burnFunctionAfterBalanceStore evm holder value).get? "from" =
      some (burnFunctionFromValue holder) := by
  rw [burnFunctionAfterBalanceStore, store_get_ne _ _ (by decide),
    burnFunctionCallStore_from]

theorem burnFunctionAfterBalanceStore_value (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    (burnFunctionAfterBalanceStore evm holder value).get? "value" =
      some (burnFunctionValueValue value) := by
  rw [burnFunctionAfterBalanceStore, store_get_ne _ _ (by decide),
    burnFunctionCallStore_value]

theorem burnFunctionAfterBalanceStore_fromBalance (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterBalanceStore evm holder value).get? "fromBalance" =
      some (burnFunctionFromBalanceValue evm holder) := by
  rw [burnFunctionAfterBalanceStore, store_get_self]

theorem burnFunctionAfterBalanceStore_totalSupply (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterBalanceStore evm holder value).get? "totalSupply" = none := by
  rw [burnFunctionAfterBalanceStore, store_get_ne _ _ (by decide),
    burnFunctionCallStore_totalSupply]

theorem burnFunctionAfterTotalSupplyStore_value (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterTotalSupplyStore evm holder value).get? "value" =
      some (burnFunctionValueValue value) := by
  rw [burnFunctionAfterTotalSupplyStore, store_get_ne _ _ (by decide),
    burnFunctionAfterBalanceStore_value]

theorem burnFunctionAfterTotalSupplyStore_totalSupply (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterTotalSupplyStore evm holder value).get? "totalSupply" = none := by
  rw [burnFunctionAfterTotalSupplyStore, store_get_ne _ _ (by decide),
    burnFunctionAfterBalanceStore_totalSupply]

theorem burnFunctionAfterTotalSupplyStore_totalSupplyLocal (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterTotalSupplyStore evm holder value).get? "_totalSupply" =
      some (burnFunctionTotalSupplyValue evm holder value) := by
  rw [burnFunctionAfterTotalSupplyStore, store_get_self]

theorem evalExpr_burnFunction_from (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    evalExpr? config { contract := contract, locals := burnFunctionCallStore holder value } evm
      (.var "from") = .ok (burnFunctionFromValue holder) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionCallStore_from]

theorem evalExpr_burnFunction_value (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    evalExpr? config { contract := contract, locals := burnFunctionCallStore holder value } evm
      (.var "value") = .ok (burnFunctionValueValue value) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionCallStore_value]

theorem evalExpr_burnFunction_value_afterBalance (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm'
      (.var "value") = .ok (burnFunctionValueValue value) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionAfterBalanceStore_value]

theorem evalExpr_burnFunction_from_afterBalance (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm'
      (.var "from") = .ok (burnFunctionFromValue holder) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionAfterBalanceStore_from]

theorem evalExpr_burnFunction_value_afterTotalSupply (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      evm' (.var "value") = .ok (burnFunctionValueValue value) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionAfterTotalSupplyStore_value]

theorem evalExpr_burnFunction_fromBalance (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm'
      (.var "fromBalance") = .ok (burnFunctionFromBalanceValue evm holder) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionAfterBalanceStore_fromBalance]

theorem evalExpr_burnFunction_totalSupplyLocal (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      evm' (.var "_totalSupply") = .ok (burnFunctionTotalSupplyValue evm holder value) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnFunctionAfterTotalSupplyStore_totalSupplyLocal]

theorem evalStorageRef_burnFunction_from_balance (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalStorageRef config { contract := contract, locals := burnFunctionCallStore holder value }
      evm (balanceOfRef (.var "from")) = .ok (burnFunctionFromEvaledRef holder) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    burnFunctionFromEvaledRef, burnFunctionFromValue, burnFunctionFromKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_burnFunction_from]

theorem evalStorageRef_burnFunction_from_balance_afterBalance (evm evm' : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalStorageRef config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm'
      (balanceOfRef (.var "from")) = .ok (burnFunctionFromEvaledRef holder) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    burnFunctionFromEvaledRef, burnFunctionFromValue, burnFunctionFromKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_burnFunction_from_afterBalance]

theorem evalExpr_burnFunction_from_balance (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    evalExpr? config { contract := contract, locals := burnFunctionCallStore holder value } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (burnFunctionFromBalanceValue evm holder) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_burnFunction_from_balance evm holder value)
    (hty := by simp [storageTypeAt?, burnFunctionFromEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [burnFunctionFromSlot, burnFunctionFromBalanceWord, uniswapStorageLocLoad_uint256]

theorem evalExpr_burnFunction_balance_require_true (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (henough : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterBalanceStore_fromBalance, burnFunctionAfterBalanceStore_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_burnFunction_balance_debit (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (henough : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm
      (.binary .sub (.var "fromBalance") (.var "value")) =
        .ok (burnFunctionBalanceDebitValue evm holder value) := by
  have hsub :
      Int.ofNat (burnFunctionFromBalanceWord evm holder).toNat - Int.ofNat value.toNat =
        Int.ofNat ((burnFunctionFromBalanceWord evm holder).toNat - value.toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (burnFunctionBalanceDebitWord evm holder value).toNat =
        (burnFunctionFromBalanceWord evm holder).toNat - value.toNat := by
    unfold burnFunctionBalanceDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (burnFunctionFromBalanceWord evm holder).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterBalanceStore_fromBalance, burnFunctionAfterBalanceStore_value]
  change EvalResult.ok (Value.int
      (Int.ofNat (burnFunctionFromBalanceWord evm holder).toNat - Int.ofNat value.toNat)) =
    EvalResult.ok (Value.int (Int.ofNat (burnFunctionBalanceDebitWord evm holder value).toNat))
  rw [hsub, htoNat]

theorem burnFunctionAssignBalance (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm
      .storage (balanceOfRef (.var "from")) (burnFunctionBalanceDebitValue evm holder value) =
        .ok ({ contract := contract, locals := burnFunctionAfterBalanceStore evm holder value },
          burnFunctionAfterBalanceState evm holder value) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [balanceOfRef])
      (her := evalStorageRef_burnFunction_from_balance_afterBalance evm evm holder value)
      (hty := by simp [storageTypeAt?, burnFunctionFromEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [burnFunctionAfterBalanceState, burnFunctionFromSlot, burnFunctionBalanceDebitWord]

theorem burnFunctionAfterBalance_codeOwner (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    (burnFunctionAfterBalanceState evm holder value).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [burnFunctionAfterBalanceState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

theorem evalStorageRef_burnFunction_totalSupply (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalStorageRef config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value) totalSupplyRef =
        .ok ({ base := "totalSupply", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]

theorem evalStorageRef_burnFunction_totalSupply_afterTotalSupply (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalStorageRef config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value) totalSupplyRef =
        .ok ({ base := "totalSupply", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]

theorem evalExpr_burnFunction_totalSupply (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value) (.storage totalSupplyRef) =
        .ok (burnFunctionTotalSupplyValue evm holder value) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [totalSupplyRef])
    (her := evalStorageRef_burnFunction_totalSupply evm holder value)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  simp [burnFunctionTotalSupplyValue, burnFunctionTotalSupplyWord,
    uniswapStorageLocLoad_uint256, burnFunctionAfterBalance_codeOwner]

theorem evalExpr_burnFunction_totalSupply_require_true (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (henough : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value)
      (.binary .ge (.var "_totalSupply") (.var "value")) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterTotalSupplyStore_totalSupplyLocal,
    burnFunctionAfterTotalSupplyStore_value]
  simp [evalBinaryOp?]
  exact henough

theorem evalExpr_burnFunction_totalSupply_debit (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (henough : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value)
      (.binary .sub (.var "_totalSupply") (.var "value")) =
        .ok (burnFunctionTotalSupplyDebitValue evm holder value) := by
  have hsub :
      Int.ofNat (burnFunctionTotalSupplyWord evm holder value).toNat - Int.ofNat value.toNat =
        Int.ofNat ((burnFunctionTotalSupplyWord evm holder value).toNat - value.toNat) := by
    exact (Int.ofNat_sub henough).symm
  have htoNat :
      (burnFunctionTotalSupplyDebitWord evm holder value).toNat =
        (burnFunctionTotalSupplyWord evm holder value).toNat - value.toNat := by
    unfold burnFunctionTotalSupplyDebitWord
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (burnFunctionTotalSupplyWord evm holder value).val.isLt)
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterTotalSupplyStore_totalSupplyLocal,
    burnFunctionAfterTotalSupplyStore_value]
  change EvalResult.ok (Value.int
      (Int.ofNat (burnFunctionTotalSupplyWord evm holder value).toNat -
        Int.ofNat value.toNat)) =
    EvalResult.ok
      (Value.int (Int.ofNat (burnFunctionTotalSupplyDebitWord evm holder value).toNat))
  rw [hsub, htoNat]

theorem burnFunctionAssignTotalSupply (evm : EVM.State) (holder : AccountAddress)
    (value : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value) .storage totalSupplyRef
      (burnFunctionTotalSupplyDebitValue evm holder value) =
        .ok
          ((show Frame from
            { contract := contract,
              locals := burnFunctionAfterTotalSupplyStore evm holder value }),
          burnFunctionPostState evm holder value) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [totalSupplyRef])
      (her := evalStorageRef_burnFunction_totalSupply_afterTotalSupply evm holder value)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [burnFunctionPostState, burnFunctionTotalSupplyDebitWord,
    burnFunctionAfterBalance_codeOwner]

theorem uniswapLookupBurnFunction :
    lookupCallable? contract "_burn" = some burnFunction.toCallable := by
  rfl

theorem bindParams_burnFunction_call (holder : AccountAddress) (value : UInt256) :
    bindParams? burnFunction.params [burnFunctionFromValue holder, burnFunctionValueValue value] =
      some (burnFunctionCallStore holder value) := by
  simp [bindParams?, burnFunction, burnFunctionCallStore, burnFunctionFromValue,
    burnFunctionValueValue]

theorem uniswapBurnFunctionBody (evm : EVM.State) (holder : AccountAddress) (value : UInt256)
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat)
    (hsupply : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat) :
    ExecFuncBody config { contract := contract, locals := burnFunctionCallStore holder value } evm
      burnFunction.body
      (.returned { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
        (burnFunctionPostState evm holder value) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := burnFunctionCallStore holder value } evm
    [ .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
      .require (.binary .ge (.var "fromBalance") (.var "value")),
      .assign .storage (balanceOfRef (.var "from"))
        (.binary .sub (.var "fromBalance") (.var "value")),
      .letDecl "_totalSupply" (some uint256) (.storage totalSupplyRef),
      .require (.binary .ge (.var "_totalSupply") (.var "value")),
      .assign .storage totalSupplyRef (.binary .sub (.var "_totalSupply") (.var "value")) ]
    (.ok { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionPostState evm holder value))
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burnFunction_from_balance evm holder value)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burnFunction_balance_require_true evm holder value hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_burnFunction_balance_debit evm holder value hbalance)
      (burnFunctionAssignBalance evm holder value)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burnFunction_totalSupply evm holder value)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burnFunction_totalSupply_require_true evm holder value hsupply)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_burnFunction_totalSupply_debit evm holder value hsupply)
      (burnFunctionAssignTotalSupply evm holder value))
    ExecBlock.nil

theorem uniswapBurnFunctionCallSuccess {caller : Frame} {evm : EVM.State}
    {holder : AccountAddress} {value : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [burnFunctionFromValue holder, burnFunctionValueValue value])
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat)
    (hsupply : value.toNat ≤ (burnFunctionTotalSupplyWord evm holder value).toNat) :
    ExecStmt config caller evm (.internalCall "_burn" args retVar)
      (.ok (resumeAfterInternalCall caller retVar none) (burnFunctionPostState evm holder value)) := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm)
    (calleeEvm := burnFunctionPostState evm holder value)
    (name := "_burn") (retVar := retVar) (args := args)
    (argVals := [burnFunctionFromValue holder, burnFunctionValueValue value])
    (callee := burnFunction) (locals := burnFunctionCallStore holder value)
    (calleeSolm := { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value })
    (value := none)
    hargs
    (by simpa [hcontract] using uniswapLookupBurnFunction)
    (bindParams_burnFunction_call holder value)
    (by
      simpa [hcontract] using
        (uniswapBurnFunctionBody evm holder value hbalance hsupply))

end UniswapV2Pair
