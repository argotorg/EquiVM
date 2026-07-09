import Examples.UniswapV2Pair.Common
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace UniswapV2Pair

/-! # Shared `_mint` source helpers -/

abbrev mintFunctionToValue (recipient : AccountAddress) : Value :=
  .address recipient

abbrev mintFunctionValueValue (value : UInt256) : Value :=
  uniswapUint256Value value

abbrev mintFunctionToKey (recipient : AccountAddress) : KeyValue :=
  .address recipient

abbrev mintFunctionCallStore (recipient : AccountAddress) (value : UInt256) : Store :=
  ((∅ : Store).insert "value" (mintFunctionValueValue value)).insert "to"
    (mintFunctionToValue recipient)

def mintFunctionTotalSupplyWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩

def mintFunctionTotalSupplyNewNat (evm : EVM.State) (value : UInt256) : Nat :=
  (mintFunctionTotalSupplyWord evm).toNat + value.toNat

def mintFunctionTotalSupplyNewWord (evm : EVM.State) (value : UInt256) : UInt256 :=
  UInt256.ofNat (mintFunctionTotalSupplyNewNat evm value)

abbrev mintFunctionTotalSupplyNewValue (evm : EVM.State) (value : UInt256) : Value :=
  uniswapUint256Value (mintFunctionTotalSupplyNewWord evm value)

def mintFunctionAfterTotalSupplyState (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (mintFunctionTotalSupplyNewWord evm value)

def mintFunctionToSlot (recipient : AccountAddress) : UInt256 :=
  balanceOfSlot (mintFunctionToKey recipient)

def mintFunctionToBalanceWord (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    UInt256 :=
  Solm.EVM.storageLoad (mintFunctionAfterTotalSupplyState evm value)
    evm.executionEnv.codeOwner (mintFunctionToSlot recipient)

def mintFunctionToBalanceNewNat
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) : Nat :=
  (mintFunctionToBalanceWord evm recipient value).toNat + value.toNat

def mintFunctionToBalanceNewWord
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) : UInt256 :=
  UInt256.ofNat (mintFunctionToBalanceNewNat evm recipient value)

abbrev mintFunctionToBalanceNewValue
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) : Value :=
  uniswapUint256Value (mintFunctionToBalanceNewWord evm recipient value)

def mintFunctionPostState (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    EVM.State :=
  Solm.EVM.storageStore (mintFunctionAfterTotalSupplyState evm value)
    evm.executionEnv.codeOwner (mintFunctionToSlot recipient)
    (mintFunctionToBalanceNewWord evm recipient value)

def mintFunctionToEvaledRef (recipient : AccountAddress) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (mintFunctionToKey recipient)] }

theorem mintFunctionCallStore_to (recipient : AccountAddress) (value : UInt256) :
    (mintFunctionCallStore recipient value).get? "to" =
      some (mintFunctionToValue recipient) := by
  rw [mintFunctionCallStore, store_get_self]

theorem mintFunctionCallStore_value (recipient : AccountAddress) (value : UInt256) :
    (mintFunctionCallStore recipient value).get? "value" =
      some (mintFunctionValueValue value) := by
  rw [mintFunctionCallStore, store_get_ne _ _ (by decide), store_get_self]

theorem mintFunctionCallStore_totalSupply (recipient : AccountAddress) (value : UInt256) :
    (mintFunctionCallStore recipient value).get? "totalSupply" = none := by
  rw [mintFunctionCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem mintFunctionCallStore_balanceOf (recipient : AccountAddress) (value : UInt256) :
    (mintFunctionCallStore recipient value).get? "balanceOf" = none := by
  rw [mintFunctionCallStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_mintFunction_value (evm : EVM.State) (recipient : AccountAddress)
    (value : UInt256) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value } evm
      (.var "value") = .ok (mintFunctionValueValue value) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFunctionCallStore_value]

theorem evalExpr_mintFunction_to
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value } evm
      (.var "to") = .ok (mintFunctionToValue recipient) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [mintFunctionCallStore_to]

theorem evalStorageRef_mintFunction_totalSupply
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    evalStorageRef config { contract := contract, locals := mintFunctionCallStore recipient value }
      evm
      totalSupplyRef = .ok ({ base := "totalSupply", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef, EvalResult.bind, pure, bind]

theorem evalExpr_mintFunction_totalSupply
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value } evm
      (.storage totalSupplyRef) = .ok (uniswapUint256Value (mintFunctionTotalSupplyWord evm)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [totalSupplyRef])
    (her := evalStorageRef_mintFunction_totalSupply evm recipient value)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm ⟨0⟩)

set_option maxHeartbeats 1000000 in
theorem evalExpr_mintFunction_totalSupply_add
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hfit : mintFunctionTotalSupplyNewNat evm value < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value } evm
      (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))) =
        .ok (mintFunctionTotalSupplyNewValue evm value) := by
  have hlt : ¬ Int.ofNat (mintFunctionTotalSupplyNewNat evm value) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have htoNat :
      (UInt256.ofNat (mintFunctionTotalSupplyNewNat evm value)).toNat =
        mintFunctionTotalSupplyNewNat evm value := by
    exact ulit_toNat' _ hfit
  have hguard :
      ¬ (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat + Int.ofNat value.toNat < 0 ∨
        (2 : Int) ^ 256 ≤
          Int.ofNat (mintFunctionTotalSupplyWord evm).toNat + Int.ofNat value.toNat) := by
    push Not
    constructor
    · exact Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat :
          (mintFunctionTotalSupplyWord evm).toNat + value.toNat < 2 ^ 256 := by
        simpa [mintFunctionTotalSupplyNewNat, UInt256.size] using hfit
      simpa [Nat.cast_add] using Int.ofNat_lt.mpr hfitNat
  simp only [u256, evalExpr?, evalExpr_mintFunction_totalSupply evm recipient value,
    evalExpr_mintFunction_value evm recipient value, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  have hguardBool :
      ¬ ((decide (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat +
          Int.ofNat value.toNat < 0) ||
        decide (Int.ofNat (mintFunctionTotalSupplyWord evm).toNat +
          Int.ofNat value.toNat ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  rw [if_neg hguardBool]
  have htoNat' :
      (UInt256.ofNat ((mintFunctionTotalSupplyWord evm).toNat + value.toNat)).toNat =
        (mintFunctionTotalSupplyWord evm).toNat + value.toNat := by
    simpa [mintFunctionTotalSupplyNewNat] using htoNat
  simp [mintFunctionTotalSupplyNewValue, mintFunctionTotalSupplyNewWord,
    mintFunctionTotalSupplyNewNat, uniswapUint256Value, uint256Value, htoNat', Nat.cast_add]

theorem mintFunctionAssignTotalSupply
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := mintFunctionCallStore recipient value }
      evm .storage totalSupplyRef (mintFunctionTotalSupplyNewValue evm value) =
        .ok ({ contract := contract, locals := mintFunctionCallStore recipient value },
          mintFunctionAfterTotalSupplyState evm value) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [totalSupplyRef])
      (her := evalStorageRef_mintFunction_totalSupply evm recipient value)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [mintFunctionAfterTotalSupplyState, mintFunctionTotalSupplyNewWord]

theorem mintFunctionAfterTotalSupply_codeOwner (evm : EVM.State) (value : UInt256) :
    (mintFunctionAfterTotalSupplyState evm value).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp only [mintFunctionAfterTotalSupplyState, Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? evm.executionEnv.codeOwner with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

theorem evalStorageRef_mintFunction_to_balance (evm' : EVM.State)
    (recipient : AccountAddress) (value : UInt256) :
    evalStorageRef config { contract := contract, locals := mintFunctionCallStore recipient value }
      evm' (balanceOfRef (.var "to")) = .ok (mintFunctionToEvaledRef recipient) := by
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, balanceOfRef,
    mintFunctionToEvaledRef, mintFunctionToValue, mintFunctionToKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr_mintFunction_to]

theorem evalExpr_mintFunction_to_balance
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value }
      (mintFunctionAfterTotalSupplyState evm value) (.storage (balanceOfRef (.var "to"))) =
        .ok (uniswapUint256Value (mintFunctionToBalanceWord evm recipient value)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [balanceOfRef])
    (her := evalStorageRef_mintFunction_to_balance
      (mintFunctionAfterTotalSupplyState evm value) recipient value)
    (hty := by simp [storageTypeAt?, mintFunctionToEvaledRef, contract, storageDecls,
      uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [mintFunctionToSlot, mintFunctionToBalanceWord, uniswapStorageLocLoad_uint256,
    mintFunctionAfterTotalSupply_codeOwner]

set_option maxHeartbeats 1000000 in
theorem evalExpr_mintFunction_to_balance_add
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hfit : mintFunctionToBalanceNewNat evm recipient value < UInt256.size) :
    evalExpr? config { contract := contract, locals := mintFunctionCallStore recipient value }
      (mintFunctionAfterTotalSupplyState evm value)
      (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) =
        .ok (mintFunctionToBalanceNewValue evm recipient value) := by
  have hlt :
      ¬ Int.ofNat (mintFunctionToBalanceNewNat evm recipient value) ≥ (2 : Int) ^ 256 := by
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have htoNat :
      (UInt256.ofNat (mintFunctionToBalanceNewNat evm recipient value)).toNat =
        mintFunctionToBalanceNewNat evm recipient value := by
    exact ulit_toNat' _ hfit
  have hguard :
      ¬ (Int.ofNat (mintFunctionToBalanceWord evm recipient value).toNat +
          Int.ofNat value.toNat < 0 ∨
        (2 : Int) ^ 256 ≤
          Int.ofNat (mintFunctionToBalanceWord evm recipient value).toNat +
            Int.ofNat value.toNat) := by
    push Not
    constructor
    · exact Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat :
          (mintFunctionToBalanceWord evm recipient value).toNat + value.toNat < 2 ^ 256 := by
        simpa [mintFunctionToBalanceNewNat, UInt256.size] using hfit
      simpa [Nat.cast_add] using Int.ofNat_lt.mpr hfitNat
  simp only [u256, evalExpr?, evalExpr_mintFunction_to_balance evm recipient value,
    evalExpr_mintFunction_value (mintFunctionAfterTotalSupplyState evm value) recipient value,
    EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  have hguardBool :
      ¬ ((decide (Int.ofNat (mintFunctionToBalanceWord evm recipient value).toNat +
          Int.ofNat value.toNat < 0) ||
        decide (Int.ofNat (mintFunctionToBalanceWord evm recipient value).toNat +
          Int.ofNat value.toNat ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  rw [if_neg hguardBool]
  have htoNat' :
      (UInt256.ofNat
        ((mintFunctionToBalanceWord evm recipient value).toNat + value.toNat)).toNat =
        (mintFunctionToBalanceWord evm recipient value).toNat + value.toNat := by
    simpa [mintFunctionToBalanceNewNat] using htoNat
  simp [mintFunctionToBalanceNewValue, mintFunctionToBalanceNewWord,
    mintFunctionToBalanceNewNat, uniswapUint256Value, uint256Value, htoNat', Nat.cast_add]

theorem mintFunctionAssignToBalance
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256) :
    assignStorageRef? config
      { contract := contract, locals := mintFunctionCallStore recipient value }
      (mintFunctionAfterTotalSupplyState evm value) .storage (balanceOfRef (.var "to"))
      (mintFunctionToBalanceNewValue evm recipient value) =
        .ok ({ contract := contract, locals := mintFunctionCallStore recipient value },
          mintFunctionPostState evm recipient value) := by
  simp only [balanceOfRef]
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simp [mintFunctionCallStore, balanceOfRef])
      (her := evalStorageRef_mintFunction_to_balance
        (mintFunctionAfterTotalSupplyState evm value) recipient value)
      (hty := by simp [storageTypeAt?, mintFunctionToEvaledRef, contract, storageDecls,
        uint256St, storageTypeStep?])
      (hloc := by rfl)
  rw [uniswapStorageLocStore_uint256]
  simp [mintFunctionPostState, mintFunctionToSlot, mintFunctionToBalanceNewWord,
    mintFunctionAfterTotalSupply_codeOwner]

theorem uniswapLookupMintFunction :
    lookupCallable? contract "_mint" = some mintFunction.toCallable := by
  rfl

theorem bindParams_mintFunction_call (recipient : AccountAddress) (value : UInt256) :
    bindParams? mintFunction.params
      [mintFunctionToValue recipient, mintFunctionValueValue value] =
      some (mintFunctionCallStore recipient value) := by
  simp [bindParams?, mintFunction, mintFunctionCallStore, mintFunctionToValue,
    mintFunctionValueValue]

theorem uniswapMintFunctionBody
    (evm : EVM.State) (recipient : AccountAddress) (value : UInt256)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm value < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient value < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := mintFunctionCallStore recipient value }
      evm
      mintFunction.body
      (.returned { contract := contract, locals := mintFunctionCallStore recipient value }
        (mintFunctionPostState evm recipient value) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := mintFunctionCallStore recipient value } evm
    [ .assign .storage totalSupplyRef
        (u256 (.binary .add (.storage totalSupplyRef) (.var "value"))),
      .assign .storage (balanceOfRef (.var "to"))
        (u256 (.binary .add (.storage (balanceOfRef (.var "to"))) (.var "value"))) ]
    (.ok { contract := contract, locals := mintFunctionCallStore recipient value }
      (mintFunctionPostState evm recipient value))
  refine ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_mintFunction_totalSupply_add evm recipient value hfitSupply)
      (mintFunctionAssignTotalSupply evm recipient value)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign
      (evalExpr_mintFunction_to_balance_add evm recipient value hfitBalance)
      (mintFunctionAssignToBalance evm recipient value))
    ExecBlock.nil

theorem uniswapMintFunctionCallSuccess {caller : Frame} {evm : EVM.State}
    {recipient : AccountAddress} {value : UInt256} {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [mintFunctionToValue recipient, mintFunctionValueValue value])
    (hfitSupply : mintFunctionTotalSupplyNewNat evm value < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient value < UInt256.size) :
    ExecStmt config caller evm (.internalCall "_mint" args retVar)
      (.ok (resumeAfterInternalCall caller retVar none)
        (mintFunctionPostState evm recipient value)) := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := caller) (evm := evm)
    (calleeEvm := mintFunctionPostState evm recipient value)
    (name := "_mint") (retVar := retVar) (args := args)
    (argVals := [mintFunctionToValue recipient, mintFunctionValueValue value])
    (callee := mintFunction) (locals := mintFunctionCallStore recipient value)
    (calleeSolm := { contract := contract, locals := mintFunctionCallStore recipient value })
    (value := none)
    hargs
    (by simpa [hcontract] using uniswapLookupMintFunction)
    (bindParams_mintFunction_call recipient value)
    (by
      simpa [hcontract] using
        (uniswapMintFunctionBody evm recipient value hfitSupply hfitBalance))

end UniswapV2Pair
