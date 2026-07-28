import Benchmarks.CompoundIII.CometRewards.RewardConfig
import Benchmarks.CompoundIII.CometRewards.SetRewardConfigWithMultiplier
import Benchmarks.CompoundIII.CometRewards.TransferGovernor
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `setRewardConfig(address,address)` ABI and source setup -/

abbrev setRewardConfigCometWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev setRewardConfigTokenWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev setRewardConfigCometValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)

abbrev setRewardConfigTokenValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat)

abbrev setRewardConfigMultiplierValue : Value :=
  .int factorScale

abbrev setRewardConfigStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "comet" (setRewardConfigCometValue I)).insert "token"
    (setRewardConfigTokenValue I)

abbrev setRewardConfigBodyStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "multiplier" setRewardConfigMultiplierValue).insert "token"
    (setRewardConfigTokenValue I)).insert "comet" (setRewardConfigCometValue I)

abbrev setRewardConfigArgs (I : ExecutionEnv) : List Value :=
  [setRewardConfigCometValue I, setRewardConfigTokenValue I, setRewardConfigMultiplierValue]

abbrev setRewardConfigFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (setRewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }

abbrev setRewardConfigBodyFrame (_evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := setRewardConfigBodyStore I }

def setRewardConfigSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardConfigSlot (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))

theorem setRewardConfigSlotOf_eq_solc (I : ExecutionEnv)
    (hcanon : (setRewardConfigCometWord I).toNat < EVM.addressModulus) :
    setRewardConfigSlotOf I = solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I) := by
  unfold setRewardConfigSlotOf rewardConfigSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  rfl

theorem setRewardConfigStore_comet (I : ExecutionEnv) :
    (setRewardConfigStore I).get? "comet" = some (setRewardConfigCometValue I) := by
  rw [setRewardConfigStore, store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigStore_token (I : ExecutionEnv) :
    (setRewardConfigStore I).get? "token" = some (setRewardConfigTokenValue I) := by
  rw [setRewardConfigStore, store_get_self]

theorem setRewardConfigBodyStore_comet (I : ExecutionEnv) :
    (setRewardConfigBodyStore I).get? "comet" = some (setRewardConfigCometValue I) := by
  rw [setRewardConfigBodyStore, store_get_self]

theorem setRewardConfigBodyStore_token (I : ExecutionEnv) :
    (setRewardConfigBodyStore I).get? "token" = some (setRewardConfigTokenValue I) := by
  rw [setRewardConfigBodyStore, store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigBodyStore_multiplier (I : ExecutionEnv) :
    (setRewardConfigBodyStore I).get? "multiplier" = some setRewardConfigMultiplierValue := by
  rw [setRewardConfigBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigBodyStore_governor (I : ExecutionEnv) :
    (setRewardConfigBodyStore I).get? "governor" = none := by
  rw [setRewardConfigBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem setRewardConfigBodyStore_rewardConfig (I : ExecutionEnv) :
    (setRewardConfigBodyStore I).get? "rewardConfig" = none := by
  rw [setRewardConfigBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_setRewardConfig_comet (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigFrame evm I) evm (.var "comet") =
      .ok (setRewardConfigCometValue I) := by
  simp only [setRewardConfigFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), setRewardConfigStore_comet]

theorem evalExpr_setRewardConfig_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigFrame evm I) evm (.var "token") =
      .ok (setRewardConfigTokenValue I) := by
  simp only [setRewardConfigFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), setRewardConfigStore_token]

theorem evalExpr_setRewardConfig_factorScale (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigFrame evm I) evm (.intLit factorScale) =
      .ok setRewardConfigMultiplierValue := by
  unfold evalExpr? setRewardConfigMultiplierValue
  rfl

theorem evalExprs_setRewardConfig_args (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config (setRewardConfigFrame evm I) evm
      [.var "comet", .var "token", (.intLit factorScale)] =
        .ok (setRewardConfigArgs I) := by
  simp only [setRewardConfigArgs, evalExprs?, evalExpr_setRewardConfig_comet,
    evalExpr_setRewardConfig_token, evalExpr_setRewardConfig_factorScale,
    EvalResult.bind, bind]
  rfl

theorem evalExpr_setRewardConfig_body_comet (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm (.var "comet") =
      .ok (setRewardConfigCometValue I) := by
  simp only [setRewardConfigBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigBodyStore_comet]

theorem evalExpr_setRewardConfig_body_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm (.var "token") =
      .ok (setRewardConfigTokenValue I) := by
  simp only [setRewardConfigBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigBodyStore_token]

theorem evalExpr_setRewardConfig_body_multiplier (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm (.var "multiplier") =
      .ok setRewardConfigMultiplierValue := by
  simp only [setRewardConfigBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigBodyStore_multiplier]

theorem lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig :
    lookupCallable? contract "setRewardConfigWithMultiplierBody" =
      some setRewardConfigWithMultiplierFunction.toCallable := by
  rfl

theorem bindParams_setRewardConfigWithMultiplier_from_setRewardConfig (I : ExecutionEnv) :
    bindParams? setRewardConfigWithMultiplierFunction.params (setRewardConfigArgs I) =
      some (setRewardConfigBodyStore I) := by
  simp [setRewardConfigWithMultiplierFunction, setRewardConfigArgs, setRewardConfigBodyStore,
    setRewardConfigCometValue, setRewardConfigTokenValue, setRewardConfigMultiplierValue,
    bindParams?, factorScale]

theorem evalExpr_setRewardConfig_body_governor (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm (.storage governorRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (setRewardConfigBodyFrame evm I) evm
      governorRef = .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar
    (hbase := by
      change (setRewardConfigBodyStore I).get? "governor" = none
      exact setRewardConfigBodyStore_governor I)
    (her := her) (hty := hty) (hloc := by rfl),
    cometRewardsStorageLocLoad_address_offset0]

theorem evalExpr_setRewardConfig_body_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setRewardConfig_body_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setRewardConfig_body_sender,
    evalExpr_setRewardConfig_body_governor, bind, EvalResult.bind, evalBinaryOp?]
  have haddr :
      evm.executionEnv.source ≠
        AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat := by
    intro haddr
    exact hgov (by
      exact solcWord_eq_of_maskedAddress_eq_source (I := evm.executionEnv) haddr.symm)
  rw [show ((.address evm.executionEnv.source : Value) ==
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)) = false by
    simp [BEq.beq, haddr]]

theorem evalExpr_setRewardConfig_body_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfig_body_sender,
    evalExpr_setRewardConfig_body_governor, bind, EvalResult.bind, evalBinaryOp?]
  rw [solcMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) hgov]
  simp [BEq.beq]

theorem evalStorageRef_setRewardConfig_body_rewardConfig_field
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef config (setRewardConfigBodyFrame evm I) evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (setRewardConfigCometWord I).toNat)),
                        .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [setRewardConfigBodyStore_comet]

theorem evalExpr_setRewardConfig_body_rewardConfig_token (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm
      (.storage (rewardConfigF (.var "comet") "token")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigSlotOf I))
            solcAddrMask).toNat)) := by
  have her := evalStorageRef_setRewardConfig_body_rewardConfig_field evm I "token"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigCometWord I).toNat)),
                  .field "token"] } =
      some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigCometWord I).toNat)),
                  .field "token"] } =
      fun _ => some (fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 0
        20 (by decide) .address) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change (setRewardConfigBodyStore I).get? "rewardConfig" = none
      exact setRewardConfigBodyStore_rewardConfig I)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_address_offset0 evm (setRewardConfigSlotOf I)

theorem evalExpr_setRewardConfig_body_zeroAddr (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem setRewardConfigAccountAddress_ofNat_masked_ne_zero_of_ne (w : UInt256)
    (h : UInt256.land w solcAddrMask ≠ ⟨0⟩) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat ≠ AccountAddress.ofNat 0 := by
  intro haddr
  apply h
  apply u256_inj
  have hval := congrArg (fun a : AccountAddress => a.val) haddr
  have hcanon := solcAddrMask_result_canonical w
  have hmod :
      (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land w solcAddrMask).toNat := by
    exact Nat.mod_eq_of_lt (by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
  simp [AccountAddress.ofNat, hmod] at hval
  simpa [UInt256.toNat] using hval

theorem evalExpr_setRewardConfig_body_token_zero_true (evm : EVM.State)
    (I : ExecutionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm
      (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr) =
        .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfig_body_rewardConfig_token,
    evalExpr_setRewardConfig_body_zeroAddr, bind, EvalResult.bind, evalBinaryOp?]
  rw [htoken]
  simp [BEq.beq]

theorem evalExpr_setRewardConfig_body_token_zero_false (evm : EVM.State)
    (I : ExecutionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    evalExpr? config (setRewardConfigBodyFrame evm I) evm
      (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr) =
        .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setRewardConfig_body_rewardConfig_token,
    evalExpr_setRewardConfig_body_zeroAddr, bind, EvalResult.bind, evalBinaryOp?]
  have haddr := setRewardConfigAccountAddress_ofNat_masked_ne_zero_of_ne
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I)) htoken
  rw [show ((.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigSlotOf I))
            solcAddrMask).toNat) : Value) ==
        .address (AccountAddress.ofNat 0)) = false by
    simp [BEq.beq, haddr]]

theorem setRewardConfigFunctionBodyReverts_auth
    (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [setRewardConfigWithMultiplierFunction] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_setRewardConfig_body_auth_false evm I hgov))

theorem setRewardConfigFunctionBodyReverts_configured
    (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [setRewardConfigWithMultiplierFunction] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov))
      (ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_setRewardConfig_body_token_zero_false evm I htoken)))

theorem setRewardConfigFunctionBodyReverts_baseCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (false, evm', out) false) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (cfg := config) (evm := evm) (evm' := evm')
      (solm := { contract := contract, locals := setRewardConfigBodyStore I })
      (receiver := .var "comet") (retVar := "accrualScale") (name := "baseAccrualScale")
      (target := AccountAddress.ofNat (setRewardConfigCometWord I).toNat)
      (eth := .intLit 0) (sendVal := 0) (args := []) (argVals := []) (out := out)
      (perm := false)
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcall)

theorem setRewardConfigFunctionBodyReverts_baseDecodeFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "baseAccrualScale" out = none) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcall hdec)

theorem setRewardConfigFunctionBodyReverts_decimalsCallFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (false, evmDec, decOut) false) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (cfg := config) (evm := evmBase) (evm' := evmDec)
      (solm :=
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale" baseValue })
      (receiver := .var "token") (retVar := "tokenDecimals") (name := "decimals")
      (target := AccountAddress.ofNat (setRewardConfigTokenWord I).toNat)
      (eth := .intLit 0) (sendVal := 0) (args := []) (argVals := []) (out := decOut)
      (perm := false)
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec)

theorem setRewardConfigFunctionBodyReverts_decimalsDecodeFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = none) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec)

theorem setRewardConfigFunctionBodyReverts_pow10Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hgt : 77 < decNat) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  let afterDecimals : Frame :=
    { contract := contract,
      locals :=
        ((setRewardConfigBodyStore I).insert "accrualScale" baseValue).insert
          "tokenDecimals" (.int (Int.ofNat decNat)) }
  have hpowArgs :
      evalExprs? config afterDecimals evmDec [.var "tokenDecimals"] =
        .ok [.int (Int.ofNat decNat)] := by
    simp only [afterDecimals, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := config) (caller := afterDecimals) (evm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa [afterDecimals] using pow10FunctionBodyReverts_gt77 evmDec hgt))

theorem setRewardConfigFunctionBodyReverts_safe64Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hgt64 : 2 ^ 64 - 1 < (10 : ℕ) ^ decNat) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  let afterDecimals : Frame :=
    { contract := contract,
      locals :=
        ((setRewardConfigBodyStore I).insert "accrualScale" baseValue).insert
          "tokenDecimals" (.int (Int.ofNat decNat)) }
  have hpowArgs :
      evalExprs? config afterDecimals evmDec [.var "tokenDecimals"] =
        .ok [.int (Int.ofNat decNat)] := by
    simp only [afterDecimals, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := afterDecimals) (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  let afterPow10 : Frame :=
    resumeAfterInternalCall afterDecimals "tokenScale256"
      (some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
  have hsafeArgs :
      evalExprs? config afterPow10 evmDec [.var "tokenScale256"] =
        .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [afterPow10, afterDecimals, resumeAfterInternalCall, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  exact ExecBlock.consRevert
    (internalCallFunctionRevert
      (cfg := config) (caller := afterPow10) (evm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa [afterPow10] using safe64FunctionBodyReverts_gt evmDec hgt64))

abbrev setRewardConfigMultiplierWord : UInt256 :=
  ⟨1000000000000000000⟩

theorem setRewardConfigMultiplierValue_eq_word :
    setRewardConfigMultiplierValue = .int (Int.ofNat setRewardConfigMultiplierWord.toNat) := by
  unfold setRewardConfigMultiplierValue setRewardConfigMultiplierWord factorScale
  native_decide

def setRewardConfigWrapperSourceAfterToken (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I)
    (setRewardConfigSlot0AfterToken
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
      (setRewardConfigTokenWord I))

def setRewardConfigWrapperSourceAfterRescale (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) : EVM.State :=
  Solm.EVM.storageStore (setRewardConfigWrapperSourceAfterToken evm I)
    (setRewardConfigWrapperSourceAfterToken evm I).executionEnv.codeOwner
    (setRewardConfigSlotOf I)
    (setRewardConfigUInt64Offset20Word
      (Solm.EVM.storageLoad (setRewardConfigWrapperSourceAfterToken evm I)
        (setRewardConfigWrapperSourceAfterToken evm I).executionEnv.codeOwner
        (setRewardConfigSlotOf I))
      rescale)

def setRewardConfigWrapperSourceAfterShouldUpscale (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) (shouldUpscale : Bool) : EVM.State :=
  let evmRescale := setRewardConfigWrapperSourceAfterRescale evm I rescale
  Solm.EVM.storageStore evmRescale evmRescale.executionEnv.codeOwner (setRewardConfigSlotOf I)
    (setRewardConfigBoolOffset28Word
      (Solm.EVM.storageLoad evmRescale evmRescale.executionEnv.codeOwner
        (setRewardConfigSlotOf I))
      (if shouldUpscale then ⟨1⟩ else ⟨0⟩))

def setRewardConfigWrapperSourceFinal (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) (shouldUpscale : Bool) : EVM.State :=
  let evmBool := setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale shouldUpscale
  Solm.EVM.storageStore evmBool evmBool.executionEnv.codeOwner
    (setRewardConfigSlotOf I + ⟨1⟩) setRewardConfigMultiplierWord

theorem setRewardConfigWrapperSourceFinal_false (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) :
    setRewardConfigWrapperSourceFinal evm I rescale false =
      Solm.EVM.storageStore
        (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale false)
        (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale false).executionEnv.codeOwner
        (setRewardConfigSlotOf I + ⟨1⟩) setRewardConfigMultiplierWord := by
  rfl

theorem setRewardConfigWrapperSourceFinal_true (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) :
    setRewardConfigWrapperSourceFinal evm I rescale true =
      Solm.EVM.storageStore
        (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale true)
        (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale true).executionEnv.codeOwner
        (setRewardConfigSlotOf I + ⟨1⟩) setRewardConfigMultiplierWord := by
  rfl

set_option maxHeartbeats 5000000 in
theorem setRewardConfigWrapperSourceFinal_accountMap_equiv
    (evm : EVM.State) (I : ExecutionEnv) (rescale : UInt256) (shouldUpscale : Bool) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner
        (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
          (setRewardConfigSlotOf I)
          (setRewardConfigSlot0Final
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
            (setRewardConfigTokenWord I) rescale
            (if shouldUpscale then ⟨1⟩ else ⟨0⟩)))
        (setRewardConfigSlotOf I + ⟨1⟩)
        setRewardConfigMultiplierWord)
      (setRewardConfigWrapperSourceFinal evm I rescale shouldUpscale).accountMap := by
  let owner := evm.executionEnv.codeOwner
  let slot := setRewardConfigSlotOf I
  let bit : UInt256 := if shouldUpscale then ⟨1⟩ else ⟨0⟩
  let old := Solm.EVM.storageLoad evm owner slot
  let tokenWord := setRewardConfigSlot0AfterToken old (setRewardConfigTokenWord I)
  let rescaleWord := setRewardConfigSlot0AfterRescale old (setRewardConfigTokenWord I) rescale
  let finalWord := setRewardConfigSlot0Final old (setRewardConfigTokenWord I) rescale bit
  cases hacc : evm.accountMap.find? owner with
  | none =>
      have htoken : setRewardConfigWrapperSourceAfterToken evm I = evm := by
        unfold setRewardConfigWrapperSourceAfterToken
        simpa [owner, slot] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigSlot0AfterToken old (setRewardConfigTokenWord I))
      have hrescale : setRewardConfigWrapperSourceAfterRescale evm I rescale = evm := by
        unfold setRewardConfigWrapperSourceAfterRescale
        rw [htoken]
        simpa [owner, slot] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigUInt64Offset20Word old rescale)
      have hbool :
          setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale shouldUpscale = evm := by
        unfold setRewardConfigWrapperSourceAfterShouldUpscale
        rw [hrescale]
        simpa [owner, slot, bit] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigBoolOffset28Word old bit)
      have hsource :
          setRewardConfigWrapperSourceFinal evm I rescale shouldUpscale = evm := by
        unfold setRewardConfigWrapperSourceFinal
        rw [hbool]
        simpa [owner, slot] using
          storageStore_absent evm owner hacc (slot + ⟨1⟩) setRewardConfigMultiplierWord
      have hleft :
          sstoreAccountMap owner
              (sstoreAccountMap owner evm.accountMap slot finalWord)
              (slot + ⟨1⟩) setRewardConfigMultiplierWord =
            evm.accountMap := by
        unfold sstoreAccountMap
        rw [hacc]
        simp [Option.option]
        rw [hacc]
      rw [hsource]
      simpa [owner, slot, bit, old, finalWord, hleft] using
        accountMapEquiv_refl evm.accountMap
  | some acc =>
      have hcollapse0 :
          accountMapEquiv
            (sstoreAccountMap owner evm.accountMap slot finalWord)
            (sstoreAccountMap owner
              (sstoreAccountMap owner evm.accountMap slot tokenWord) slot finalWord) :=
        accountMapEquiv_sstoreAccountMap_self_update evm.accountMap owner slot tokenWord finalWord
      have hcollapse1 :
          accountMapEquiv
            (sstoreAccountMap owner
              (sstoreAccountMap owner evm.accountMap slot tokenWord) slot finalWord)
            (sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
              slot finalWord) :=
        accountMapEquiv_sstoreAccountMap_self_update
          (sstoreAccountMap owner evm.accountMap slot tokenWord) owner slot rescaleWord finalWord
      have hcollapseSlot :
          accountMapEquiv
            (sstoreAccountMap owner evm.accountMap slot finalWord)
            (sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
              slot finalWord) :=
        accountMapEquiv.trans hcollapse0 hcollapse1
      have hcollapse :=
        accountMapEquiv_sstoreAccountMap
          (σ := sstoreAccountMap owner evm.accountMap slot finalWord)
          (τ := sstoreAccountMap owner
            (sstoreAccountMap owner
              (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
            slot finalWord)
          owner (slot + ⟨1⟩) setRewardConfigMultiplierWord hcollapseSlot
      have hsource :
          (setRewardConfigWrapperSourceFinal evm I rescale shouldUpscale).accountMap =
            sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner
                  (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
                slot finalWord)
              (slot + ⟨1⟩) setRewardConfigMultiplierWord := by
        have htokenMap :
            (setRewardConfigWrapperSourceAfterToken evm I).accountMap =
              sstoreAccountMap owner evm.accountMap slot tokenWord := by
          unfold setRewardConfigWrapperSourceAfterToken
          simpa [owner, slot, old, tokenWord] using
            storageStore_accountMap evm owner slot tokenWord
        have htokenEnv :
            (setRewardConfigWrapperSourceAfterToken evm I).executionEnv = evm.executionEnv := by
          unfold setRewardConfigWrapperSourceAfterToken
          simpa [owner, slot, old, tokenWord] using
            storageStore_executionEnv evm owner slot tokenWord
        have hloadToken :
            Solm.EVM.storageLoad (setRewardConfigWrapperSourceAfterToken evm I)
              (setRewardConfigWrapperSourceAfterToken evm I).executionEnv.codeOwner slot =
              tokenWord := by
          unfold setRewardConfigWrapperSourceAfterToken
          rw [storageStore_executionEnv]
          simpa [owner, slot, old, tokenWord] using
            storageLoad_storageStore_same_present evm owner hacc slot tokenWord
        have hloadTokenOwner :
            Solm.EVM.storageLoad (setRewardConfigWrapperSourceAfterToken evm I)
              evm.executionEnv.codeOwner slot = tokenWord := by
          simpa [htokenEnv] using hloadToken
        have hrescaleMap :
            (setRewardConfigWrapperSourceAfterRescale evm I rescale).accountMap =
              sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord := by
          unfold setRewardConfigWrapperSourceAfterRescale
          simp [setRewardConfigWrapperSourceAfterToken, owner, slot, old, tokenWord,
            rescaleWord, setRewardConfigSlot0AfterRescale, storageStore_accountMap,
            storageStore_executionEnv,
            storageLoad_storageStore_same_present evm owner hacc slot tokenWord]
        have hrescaleEnv :
            (setRewardConfigWrapperSourceAfterRescale evm I rescale).executionEnv =
              evm.executionEnv := by
          unfold setRewardConfigWrapperSourceAfterRescale
          rw [storageStore_executionEnv]
          exact htokenEnv
        have haccToken :
            ∃ acc',
              (setRewardConfigWrapperSourceAfterToken evm I).accountMap.find? owner = some acc' := by
          rw [htokenMap]
          unfold sstoreAccountMap
          rw [hacc]
          simp [Option.option]
          exact ⟨_, accountMap_find_insert_self _ _ _⟩
        rcases haccToken with ⟨accToken, haccToken⟩
        have haccTokenOwner :
            (setRewardConfigWrapperSourceAfterToken evm I).accountMap.find?
              (setRewardConfigWrapperSourceAfterToken evm I).executionEnv.codeOwner =
                some accToken := by
          simpa [htokenEnv] using haccToken
        have hloadRescale :
            Solm.EVM.storageLoad (setRewardConfigWrapperSourceAfterRescale evm I rescale)
              (setRewardConfigWrapperSourceAfterRescale evm I rescale).executionEnv.codeOwner
              slot = rescaleWord := by
          unfold setRewardConfigWrapperSourceAfterRescale
          rw [storageStore_executionEnv]
          simpa [slot, rescaleWord, setRewardConfigSlot0AfterRescale, hloadToken] using
            storageLoad_storageStore_same_present
              (setRewardConfigWrapperSourceAfterToken evm I)
              (setRewardConfigWrapperSourceAfterToken evm I).executionEnv.codeOwner
              haccTokenOwner slot rescaleWord
        have hloadRescaleOwner :
            Solm.EVM.storageLoad (setRewardConfigWrapperSourceAfterRescale evm I rescale)
              evm.executionEnv.codeOwner slot = rescaleWord := by
          simpa [hrescaleEnv] using hloadRescale
        have hboolMap :
            (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale shouldUpscale).accountMap =
              sstoreAccountMap owner
                (sstoreAccountMap owner
                  (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
                slot finalWord := by
          unfold setRewardConfigWrapperSourceAfterShouldUpscale
          simp [hrescaleMap, hrescaleEnv, hloadRescaleOwner, owner, slot, bit, finalWord,
            rescaleWord, setRewardConfigSlot0Final, setRewardConfigSlot0AfterRescale,
            storageStore_accountMap]
        have hboolEnv :
            (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale shouldUpscale).executionEnv =
              evm.executionEnv := by
          unfold setRewardConfigWrapperSourceAfterShouldUpscale
          simp [hrescaleEnv, owner, slot, bit, finalWord, setRewardConfigSlot0Final,
            storageStore_executionEnv]
        unfold setRewardConfigWrapperSourceFinal
        simp [hboolMap, hboolEnv, owner, slot, storageStore_accountMap]
      rw [hsource]
      simpa [owner, slot, bit, old, finalWord] using hcollapse

def setRewardConfigWrapperAfterDecimalsFrame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  { contract := contract,
    locals :=
      ((setRewardConfigBodyStore I).insert "accrualScale"
        (.int (Int.ofNat baseWord.toNat))).insert "tokenDecimals" (.int (Int.ofNat decNat)) }

def setRewardConfigWrapperAfterPow10Frame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  resumeAfterInternalCall (setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat)
    "tokenScale256" (some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])

def setRewardConfigWrapperAfterSafe64Frame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  resumeAfterInternalCall (setRewardConfigWrapperAfterPow10Frame I baseWord decNat)
    "tokenScale" (some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])

theorem evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) {locals : Store}
    (hcomet : locals.get? "comet" = some (setRewardConfigCometValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (setRewardConfigCometWord I).toNat)),
                        .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [hcomet]

theorem setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "rewardConfig" =
      none := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, setRewardConfigWrapperAfterPow10Frame,
    setRewardConfigWrapperAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigBodyStore_rewardConfig]

theorem setRewardConfigWrapperAfterSafe64Frame_comet (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "comet" =
      some (setRewardConfigCometValue I) := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, setRewardConfigWrapperAfterPow10Frame,
    setRewardConfigWrapperAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigBodyStore_comet]

theorem setRewardConfigWrapperAfterSafe64Frame_accrualScale (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "accrualScale" =
      some (.int (Int.ofNat baseWord.toNat)) := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, setRewardConfigWrapperAfterPow10Frame,
    setRewardConfigWrapperAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigWrapperAfterSafe64Frame_tokenScale (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "tokenScale" =
      some (.int (Int.ofNat ((10 : ℕ) ^ decNat))) := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, resumeAfterInternalCall, collapseReturns]
  rw [store_get_self]

theorem setRewardConfigWrapperAfterSafe64Frame_token (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "token" =
      some (setRewardConfigTokenValue I) := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, setRewardConfigWrapperAfterPow10Frame,
    setRewardConfigWrapperAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigBodyStore_token]

theorem setRewardConfigWrapperAfterSafe64Frame_multiplier (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat).locals.get? "multiplier" =
      some setRewardConfigMultiplierValue := by
  simp only [setRewardConfigWrapperAfterSafe64Frame, setRewardConfigWrapperAfterPow10Frame,
    setRewardConfigWrapperAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigBodyStore_multiplier]

theorem setRewardConfigWrapperAssign_token_afterSafe64 (evm : EVM.State) (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ)
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus) :
    assignStorageRef? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      evm .storage (rewardConfigF (.var "comet") "token") (setRewardConfigTokenValue I) =
      .ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat,
        setRewardConfigWrapperSourceAfterToken evm I) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)),
        .field "token"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 0 20 (by decide) .address
  have her :
      evalStorageRef config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evm
        (rewardConfigF (.var "comet") "token") = .ok er := by
    exact evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
      (evm := evm) (I := I) (field := "token")
      (setRewardConfigWrapperAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore evm loc (setRewardConfigTokenValue I) =
        some (setRewardConfigWrapperSourceAfterToken evm I) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 0 20
      (by decide) .address from rfl, slotAdd_zero]
    simpa [setRewardConfigWrapperSourceAfterToken, setRewardConfigSlot0AfterToken,
      setRewardConfigTokenValue, fieldLoc, loc, addressOffset0Loc] using
      storageLocStore_address_offset0 evm (setRewardConfigSlotOf I)
        (setRewardConfigTokenWord I) hcanonToken
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
    (evm := evm) (evm' := setRewardConfigWrapperSourceAfterToken evm I)
    (slot := rewardConfigF (.var "comet") "token") (er := er)
    (ty := .elem .address) (loc := loc) (value := setRewardConfigTokenValue I)
    (setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigWrapperAssign_rescale_afterSafe64 (evm : EVM.State)
    (I : ExecutionEnv) (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (setRewardConfigWrapperSourceAfterToken evm I) .storage
      (rewardConfigF (.var "comet") "rescaleFactor") (.int (Int.ofNat rescale.toNat)) =
      .ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat,
        setRewardConfigWrapperSourceAfterRescale evm I rescale) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)),
        .field "rescaleFactor"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 20 8 (by decide) (.int uint64Int)
  have her :
      evalStorageRef config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterToken evm I)
        (rewardConfigF (.var "comet") "rescaleFactor") = .ok er := by
    exact evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
      (evm := setRewardConfigWrapperSourceAfterToken evm I) (I := I)
      (field := "rescaleFactor")
      (setRewardConfigWrapperAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint64Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigWrapperSourceAfterToken evm I) loc
        (.int (Int.ofNat rescale.toNat)) =
        some (setRewardConfigWrapperSourceAfterRescale evm I rescale) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 20 8
      (by decide) (.int uint64Int) from rfl, slotAdd_zero]
    simpa [setRewardConfigWrapperSourceAfterRescale] using
      setRewardConfigStorageLocStore_uint64_offset20
        (setRewardConfigWrapperSourceAfterToken evm I) (setRewardConfigSlotOf I) rescale
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigWrapperSourceAfterToken evm I)
    (evm' := setRewardConfigWrapperSourceAfterRescale evm I rescale)
    (slot := rewardConfigF (.var "comet") "rescaleFactor") (er := er)
    (ty := .elem (.int uint64Int)) (loc := loc)
    (value := .int (Int.ofNat rescale.toNat))
    (setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigWrapperAssign_shouldUpscale_false_afterSafe64 (evm : EVM.State)
    (I : ExecutionEnv) (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (setRewardConfigWrapperSourceAfterRescale evm I rescale) .storage
      (rewardConfigF (.var "comet") "shouldUpscale") (.bool false) =
      .ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat,
        setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale false) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)),
        .field "shouldUpscale"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 28 1 (by decide) .bool
  have her :
      evalStorageRef config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterRescale evm I rescale)
        (rewardConfigF (.var "comet") "shouldUpscale") = .ok er := by
    exact evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
      (evm := setRewardConfigWrapperSourceAfterRescale evm I rescale) (I := I)
      (field := "shouldUpscale")
      (setRewardConfigWrapperAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .bool) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigWrapperSourceAfterRescale evm I rescale) loc (.bool false) =
        some (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale false) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 28 1
      (by decide) .bool from rfl, slotAdd_zero]
    simpa [setRewardConfigWrapperSourceAfterShouldUpscale] using
      setRewardConfigStorageLocStore_bool_false_offset28
        (setRewardConfigWrapperSourceAfterRescale evm I rescale) (setRewardConfigSlotOf I)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigWrapperSourceAfterRescale evm I rescale)
    (evm' := setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale false)
    (slot := rewardConfigF (.var "comet") "shouldUpscale") (er := er)
    (ty := .elem .bool) (loc := loc) (value := .bool false)
    (setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigWrapperAssign_shouldUpscale_true_afterSafe64 (evm : EVM.State)
    (I : ExecutionEnv) (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (setRewardConfigWrapperSourceAfterRescale evm I rescale) .storage
      (rewardConfigF (.var "comet") "shouldUpscale") (.bool true) =
      .ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat,
        setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale true) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)),
        .field "shouldUpscale"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 28 1 (by decide) .bool
  have her :
      evalStorageRef config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterRescale evm I rescale)
        (rewardConfigF (.var "comet") "shouldUpscale") = .ok er := by
    exact evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
      (evm := setRewardConfigWrapperSourceAfterRescale evm I rescale) (I := I)
      (field := "shouldUpscale")
      (setRewardConfigWrapperAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .bool) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigWrapperSourceAfterRescale evm I rescale) loc (.bool true) =
        some (setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale true) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigSlotOf I) 0) 28 1
      (by decide) .bool from rfl, slotAdd_zero]
    simpa [setRewardConfigWrapperSourceAfterShouldUpscale] using
      setRewardConfigStorageLocStore_bool_true_offset28
        (setRewardConfigWrapperSourceAfterRescale evm I rescale) (setRewardConfigSlotOf I)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigWrapperSourceAfterRescale evm I rescale)
    (evm' := setRewardConfigWrapperSourceAfterShouldUpscale evm I rescale true)
    (slot := rewardConfigF (.var "comet") "shouldUpscale") (er := er)
    (ty := .elem .bool) (loc := loc) (value := .bool true)
    (setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

set_option maxHeartbeats 5000000 in
theorem setRewardConfigWrapperAssign_multiplier_afterSafe64_state
    (evm : EVM.State) (I : ExecutionEnv) (baseWord : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      evm .storage (rewardConfigF (.var "comet") "multiplier")
      setRewardConfigMultiplierValue =
      .ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (setRewardConfigSlotOf I + ⟨1⟩) setRewardConfigMultiplierWord) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat)),
        .field "multiplier"] }
  let loc : StorageLoc := uint256Loc (setRewardConfigSlotOf I + ⟨1⟩)
  have her :
      evalStorageRef config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evm
        (rewardConfigF (.var "comet") "multiplier") = .ok er := by
    exact evalStorageRef_setRewardConfigWrapper_rewardConfig_field_of_comet
      (evm := evm) (I := I) (field := "multiplier")
      (setRewardConfigWrapperAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout er = fun _ => some loc := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigSlotOf I) 1) 0 32
      (by decide) (.int uint256Int) by
        dsimp [loc]
        rw [slotAdd_one]
        rfl]
    rfl
  have hstore :
      storageLocStore evm loc setRewardConfigMultiplierValue =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (setRewardConfigSlotOf I + ⟨1⟩) setRewardConfigMultiplierWord) := by
    let slot1 := setRewardConfigSlotOf I + ⟨1⟩
    change storageLocStore evm (uint256Loc slot1) setRewardConfigMultiplierValue =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot1
        setRewardConfigMultiplierWord)
    rw [setRewardConfigMultiplierValue_eq_word]
    exact storageLocStore_uint256 evm slot1 setRewardConfigMultiplierWord
  apply assignStorageRef_storage_scalar_value
      (er := er) (ty := .elem (.int uint256Int)) (loc := loc)
  · exact setRewardConfigWrapperAfterSafe64Frame_rewardConfig_none I baseWord decNat
  · exact her
  · exact hty
  · exact hloc
  · trivial
  · exact hstore

set_option maxHeartbeats 1000000 in
theorem setRewardConfigFunctionBodyReturns_downscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = baseWord.toNat / (10 : ℕ) ^ decNat)
    (hgt : (10 : ℕ) ^ decNat < baseWord.toNat) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body
      (.returned (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceFinal evmDec I rescale false) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    (.ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (setRewardConfigWrapperSourceFinal evmDec I rescale false))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess htokenExpr (by simp [evalExpr?, pure]) (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigWrapperAfterDecimalsFrame, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigWrapperAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigWrapperAfterPow10Frame, setRewardConfigWrapperAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool true) := by
    have hgtInt : (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      exact_mod_cast hgt
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hgtInt
  refine ExecBlock.consNormal (ExecStmt.iteTrue hcond ?_) ExecBlock.nil
  have htokenRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigWrapperAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigWrapperAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterToken evmDec I)
        (.binary .div (.var "accrualScale") (.var "tokenScale")) =
        .ok (.int (Int.ofNat rescale.toNat)) := by
    rw [hrescale]
    have hpowPos : (10 : ℕ) ^ decNat ≠ 0 := by positivity
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hpowPos]
  refine ExecBlock.consNormal
    (ExecStmt.assign hrescaleRhs
      (setRewardConfigWrapperAssign_rescale_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have hfalseRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterRescale evmDec I rescale) (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  refine ExecBlock.consNormal
    (ExecStmt.assign hfalseRhs
      (setRewardConfigWrapperAssign_shouldUpscale_false_afterSafe64
        evmDec I baseWord rescale decNat)) ?_
  have hmultRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterShouldUpscale evmDec I rescale false)
        (.var "multiplier") = .ok setRewardConfigMultiplierValue := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigWrapperAfterSafe64Frame_multiplier]
  rw [setRewardConfigWrapperSourceFinal_false]
  exact ExecBlock.consNormal
    (ExecStmt.assign hmultRhs
      (setRewardConfigWrapperAssign_multiplier_afterSafe64_state
        (setRewardConfigWrapperSourceAfterShouldUpscale evmDec I rescale false) I
        baseWord decNat))
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem setRewardConfigFunctionBodyReturns_upscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = (10 : ℕ) ^ decNat / baseWord.toNat)
    (hle : baseWord.toNat ≤ (10 : ℕ) ^ decNat)
    (hbaseNZ : baseWord.toNat ≠ 0) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body
      (.returned (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceFinal evmDec I rescale true) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    (.ok (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (setRewardConfigWrapperSourceFinal evmDec I rescale true))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess htokenExpr (by simp [evalExpr?, pure]) (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigWrapperAfterDecimalsFrame, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigWrapperAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigWrapperAfterPow10Frame, setRewardConfigWrapperAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool false) := by
    have hnotNat : ¬ (10 : ℕ) ^ decNat < baseWord.toNat := by omega
    have hnotInt : ¬ (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      intro hlt
      exact hnotNat (by exact_mod_cast hlt)
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hnotInt
  refine ExecBlock.consNormal (ExecStmt.iteFalse hcond ?_) ExecBlock.nil
  have htokenRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigWrapperAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigWrapperAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterToken evmDec I)
        (.binary .div (.var "tokenScale") (.var "accrualScale")) =
        .ok (.int (Int.ofNat rescale.toNat)) := by
    rw [hrescale]
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hbaseNZ]
  refine ExecBlock.consNormal
    (ExecStmt.assign hrescaleRhs
      (setRewardConfigWrapperAssign_rescale_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have htrueRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterRescale evmDec I rescale) (.boolLit true) =
        .ok (.bool true) := by
    simp [evalExpr?, pure]
  refine ExecBlock.consNormal
    (ExecStmt.assign htrueRhs
      (setRewardConfigWrapperAssign_shouldUpscale_true_afterSafe64
        evmDec I baseWord rescale decNat)) ?_
  have hmultRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterShouldUpscale evmDec I rescale true)
        (.var "multiplier") = .ok setRewardConfigMultiplierValue := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigWrapperAfterSafe64Frame_multiplier]
  rw [setRewardConfigWrapperSourceFinal_true]
  exact ExecBlock.consNormal
    (ExecStmt.assign hmultRhs
      (setRewardConfigWrapperAssign_multiplier_afterSafe64_state
        (setRewardConfigWrapperSourceAfterShouldUpscale evmDec I rescale true) I
        baseWord decNat))
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem setRewardConfigFunctionBodyReverts_upscaleZero
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hbase0 : baseWord.toNat = 0) :
    ExecFuncBody config (setRewardConfigBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigBodyFrame evm I) evm
    [ .require (.binary .eq sender (.storage governorRef)),
      .require (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr),
      .externalCall (.var "comet") "baseAccrualScale" (.intLit 0) [] "accrualScale" false,
      .externalCall (.var "token") "decimals" (.intLit 0) [] "tokenDecimals" false,
      .internalCall "pow10" [.var "tokenDecimals"] "tokenScale256",
      .internalCall "safe64" [.var "tokenScale256"] "tokenScale",
      .ite (.binary .gt (.var "accrualScale") (.var "tokenScale"))
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "accrualScale") (.var "tokenScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit false),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ]
        [ .assign .storage (rewardConfigF (.var "comet") "token") (.var "token"),
          .assign .storage (rewardConfigF (.var "comet") "rescaleFactor")
            (.binary .div (.var "tokenScale") (.var "accrualScale")),
          .assign .storage (rewardConfigF (.var "comet") "shouldUpscale") (.boolLit true),
          .assign .storage (rewardConfigF (.var "comet") "multiplier") (.var "multiplier") ] ]
    .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_setRewardConfig_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfig_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess htokenExpr (by simp [evalExpr?, pure]) (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigWrapperAfterDecimalsFrame, evalExprs?, evalExpr?,
      EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigWrapperAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigWrapperAfterPow10Frame, setRewardConfigWrapperAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWrapperAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool false) := by
    have hnotNat : ¬ (10 : ℕ) ^ decNat < baseWord.toNat := by
      rw [hbase0]
      exact Nat.not_lt_zero _
    have hnotInt : ¬ (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      intro hlt
      exact hnotNat (by exact_mod_cast hlt)
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hnotInt
  refine ExecBlock.consRevert (ExecStmt.iteFalse hcond ?_)
  have htokenRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat) evmDec
        (.var "token") = .ok (setRewardConfigTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigWrapperAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigWrapperAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
        (setRewardConfigWrapperSourceAfterToken evmDec I)
        (.binary .div (.var "tokenScale") (.var "accrualScale")) = .revert := by
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigWrapperAfterSafe64Frame_accrualScale,
      setRewardConfigWrapperAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hbase0]
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert hrescaleRhs)

theorem cometRewardsSetRewardConfigBodyReturns_downscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = baseWord.toNat / (10 : ℕ) ^ decNat)
    (hgt : (10 : ℕ) ^ decNat < baseWord.toNat) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body
      (.returned (resumeAfterInternalCall (setRewardConfigFrame evm I) "_set" none)
        (setRewardConfigWrapperSourceFinal evmDec I rescale false) none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        (.ok (resumeAfterInternalCall (setRewardConfigFrame evm I) "_set" none)
          (setRewardConfigWrapperSourceFinal evmDec I rescale false)) := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (calleeEvm := setRewardConfigWrapperSourceFinal evmDec I rescale false)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (calleeSolm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (value := none)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReturns_downscale
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hrescale hgt)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consNormal hstmt ExecBlock.nil)

theorem cometRewardsSetRewardConfigBodyReturns_upscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = (10 : ℕ) ^ decNat / baseWord.toNat)
    (hle : baseWord.toNat ≤ (10 : ℕ) ^ decNat)
    (hbaseNZ : baseWord.toNat ≠ 0) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body
      (.returned (resumeAfterInternalCall (setRewardConfigFrame evm I) "_set" none)
        (setRewardConfigWrapperSourceFinal evmDec I rescale true) none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        (.ok (resumeAfterInternalCall (setRewardConfigFrame evm I) "_set" none)
          (setRewardConfigWrapperSourceFinal evmDec I rescale true)) := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (calleeEvm := setRewardConfigWrapperSourceFinal evmDec I rescale true)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (calleeSolm := setRewardConfigWrapperAfterSafe64Frame I baseWord decNat)
      (value := none)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReturns_upscale
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hrescale hle hbaseNZ)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consNormal hstmt ExecBlock.nil)

theorem cometRewardsSetRewardConfigBodyReverts_upscaleZero
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hbase0 : baseWord.toNat = 0) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_upscaleZero
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hbase0)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_auth
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_auth evm I hgov)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
          (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_configured
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_configured evm I hgov htoken)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
      (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_baseCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (false, evm', out) false) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_baseCallFailure evm evm' I hgov htoken hcall)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_baseDecodeFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "baseAccrualScale" out = none) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_baseDecodeFailure evm evm' I hgov htoken hcall hdec)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_decimalsCallFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (false, evmDec, decOut) false) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_decimalsCallFailure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_decimalsDecodeFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = none) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_decimalsDecodeFailure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_pow10Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hgt : 77 < decNat) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_pow10Failure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec hgt)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigBodyReverts_safe64Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (setRewardConfigSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hgt64 : 2 ^ 64 - 1 < (10 : ℕ) ^ decNat) :
    ExecTransitionBody config contract evm (setRewardConfigStore I)
      setRewardConfigTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", (.intLit factorScale)] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", (.intLit factorScale)])
      (argVals := setRewardConfigArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigBodyStore I)
      (evalExprs_setRewardConfig_args evm I)
      (by simpa [setRewardConfigFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody_from_setRewardConfig)
      (bindParams_setRewardConfigWithMultiplier_from_setRewardConfig I)
      (by
        simpa [setRewardConfigFrame, setRewardConfigBodyFrame] using
          setRewardConfigFunctionBodyReverts_safe64Failure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hgt64)
  simpa [setRewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsDecode_setRewardConfig_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (setRewardConfigTransition.params.map Param.name)
      (transitionSignature setRewardConfigTransition).paramTypes I.calldata =
        some (setRewardConfigStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token"] [addr, addr]
    I.calldata = _
  simpa [config, setRewardConfigStore, setRewardConfigCometValue, setRewardConfigTokenValue,
    setRewardConfigCometWord, setRewardConfigTokenWord, calldataWord]
    using decodeCalldata_address_address_ok (cd := I.calldata) (x := "comet") (y := "token")
      hsz68 hbig hcanonComet hcanonToken

theorem cometRewardsDecode_setRewardConfig_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (setRewardConfigTransition.params.map Param.name)
      (transitionSignature setRewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_short
    (cd := I.calldata) (x := "comet") (y := "token") hsz4 hshort

theorem cometRewardsDecode_setRewardConfig_none_noncanon_comet {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncComet : ¬ (setRewardConfigCometWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (setRewardConfigTransition.params.map Param.name)
      (transitionSignature setRewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token"] [addr, addr]
    I.calldata = none
  simpa [config, addr, setRewardConfigCometWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon0
      (cd := I.calldata) (x := "comet") (y := "token") hsz68 hbig hncComet

theorem cometRewardsDecode_setRewardConfig_none_noncanon_token {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hncToken : ¬ (setRewardConfigTokenWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (setRewardConfigTransition.params.map Param.name)
      (transitionSignature setRewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token"] [addr, addr]
    I.calldata = none
  simpa [config, addr, setRewardConfigCometWord, setRewardConfigTokenWord, calldataWord]
    using decodeCalldata_address_address_none_noncanon1
      (cd := I.calldata) (x := "comet") (y := "token") hsz68 hbig hcanonComet hncToken

theorem cometRewardsDecode_setRewardConfig_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (setRewardConfigTransition.params.map Param.name)
      (transitionSignature setRewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token"] [addr, addr]
    I.calldata = none
  simpa [config, addr] using decodeCalldata_address_address_none_huge
    (cd := I.calldata) (x := "comet") (y := "token") hbig

theorem cometRewardsSetRewardConfigSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 7)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 7) rfl hsel

theorem cometRewardsDispatch_setRewardConfig {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 7 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some setRewardConfigTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition])
    (post := [setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition,
      transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, setRewardConfigSelectorBytes]; exact hsel)
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 7 :=
    (byteArray_eq_of_beq hsel).symm
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]
    decide
  · rw [selectorOf, governorSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardConfigSelectorBytes, hcd]
    decide
  · rw [selectorOf, rewardsClaimedSelectorBytes, hcd]
    decide

theorem cometRewardsSetRewardConfigCalldataCheckOk {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 2)
      (by simpa using hsz68) hhi hsize

theorem cometRewardsSetRewardConfigCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  simpa using
    solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 2)
      hsz4 (by simpa using hshort) hsize (by norm_num)

theorem cometRewardsSetRewardConfigCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨64⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨64⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 2)
      hbig hsize (by norm_num)

theorem cometRewardsSetRewardConfigX_shortarg
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd1009⟩ := hreach
  have rd1012 := evm_run rd1009 with [jumpdest, pop, swap1, callvalue]
  rw [hwv] at rd1012
  have rd1024 := evm_run rd1012 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1024
  exact evm_run rd1024 with [
    push2 ⟨797⟩, jumpiT (by decide) (by native_decide),
    jumpdest, dup4, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsSetRewardConfigX_hugearg
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd1009⟩ := hreach
  have rd1012 := evm_run rd1009 with [jumpdest, pop, swap1, callvalue]
  rw [hwv] at rd1012
  have rd1024 := evm_run rd1012 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1024
  exact evm_run rd1024 with [
    push2 ⟨797⟩, jumpiT (by decide) (by native_decide),
    jumpdest, dup4, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_dec1044_args
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1044⟩
      [setRewardConfigTokenWord I, ⟨224⟩, setRewardConfigCometWord I, ⟨4⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsSetRewardConfigCalldataCheckOk (I := I) hsz68 hsize hhi
  obtain ⟨_, _, rd1009⟩ := hreach
  have rd1012 := evm_run rd1009 with [jumpdest, pop, swap1, callvalue]
  rw [hwv] at rd1012
  have rd1024 := evm_run rd1012 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1024
  have rd2831 := evm_run rd1024 with [
    push2 ⟨797⟩, jumpiNT (by decide), push2 ⟨1035⟩, push2 ⟨2831⟩,
    jump (by native_decide)]
  have rd1035 := evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, and, dup3, sub, push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (setRewardConfigCometWord I) solcAddrMask =
            setRewardConfigCometWord I := by
        exact solcAddrMask_clean (by
          simpa [setRewardConfigCometWord, calldataWord] using hcanon0)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        simpa [setRewardConfigCometWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    jump (by native_decide)]
  have rd2853 := evm_run rd1035 with [
    jumpdest, swap1, push2 ⟨1044⟩, push2 ⟨2853⟩, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, and, dup3, sub, push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (setRewardConfigTokenWord I) solcAddrMask =
            setRewardConfigTokenWord I := by
        exact solcAddrMask_clean (by
          simpa [setRewardConfigTokenWord, calldataWord] using hcanon1)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        simpa [setRewardConfigTokenWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_noncanon_comet
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (setRewardConfigCometWord I)
      (UInt256.land (setRewardConfigCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigCalldataCheckOk (I := I) hsz68 hsize hhi
  obtain ⟨_, _, rd1009⟩ := hreach
  have rd1012 := evm_run rd1009 with [jumpdest, pop, swap1, callvalue]
  rw [hwv] at rd1012
  have rd1024 := evm_run rd1012 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1024
  have rd2831 := evm_run rd1024 with [
    push2 ⟨797⟩, jumpiNT (by decide), push2 ⟨1035⟩, push2 ⟨2831⟩,
    jump (by native_decide)]
  exact evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, and, dup3, sub, push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hraw :
            UInt256.eq
                (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                (UInt256.land
                  (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
                  solcAddrMask) = ⟨1⟩ := by
          rw [← heq]
          exact uInt256_eq_self _
        have hclean :
            UInt256.eq (setRewardConfigCometWord I)
                (UInt256.land (setRewardConfigCometWord I) solcAddrMask) = ⟨1⟩ := by
          simpa [setRewardConfigCometWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_noncanon_token
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (setRewardConfigTokenWord I)
      (UInt256.land (setRewardConfigTokenWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigCalldataCheckOk (I := I) hsz68 hsize hhi
  obtain ⟨_, _, rd1009⟩ := hreach
  have rd1012 := evm_run rd1009 with [jumpdest, pop, swap1, callvalue]
  rw [hwv] at rd1012
  have rd1024 := evm_run rd1012 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    dup3, push1 ⟨3⟩, not, calldatasize, add, slt]
  rw [hslt] at rd1024
  have rd2831 := evm_run rd1024 with [
    push2 ⟨797⟩, jumpiNT (by decide), push2 ⟨1035⟩, push2 ⟨2831⟩,
    jump (by native_decide)]
  have rd1035 := evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, and, dup3, sub, push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        have hclean' :
            UInt256.land (setRewardConfigCometWord I) solcAddrMask =
              setRewardConfigCometWord I := by
          exact solcAddrMask_clean (by
            simpa [setRewardConfigCometWord, calldataWord] using hcanon0)
        simpa [setRewardConfigCometWord, calldataWord] using hclean'
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]
  have rd2853 := evm_run rd1035 with [
    jumpdest, swap1, push2 ⟨1044⟩, push2 ⟨2853⟩, jump (by native_decide)]
  exact evm_run rd2853 with [
    jumpdest, push1 ⟨36⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup3, and, dup3, sub, push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hraw :
            UInt256.eq
                (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
                (UInt256.land
                  (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
                  solcAddrMask) = ⟨1⟩ := by
          rw [← heq]
          exact uInt256_eq_self _
        have hclean :
            UInt256.eq (setRewardConfigTokenWord I)
                (UInt256.land (setRewardConfigTokenWord I) solcAddrMask) = ⟨1⟩ := by
          simpa [setRewardConfigTokenWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_revert_auth
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1044⟩ :=
    cometRewardsSetRewardConfigX_dec1044_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz68 hsize hhi hcanon0 hcanon1 hreach
  have rd1047 := evm_run rd1044 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨_, _, rd1048₀⟩ := rd1047.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1048⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1048⟩
      [governorWord σ I, setRewardConfigTokenWord I, ⟨224⟩,
        setRewardConfigCometWord I, ⟨4⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd1048₀⟩
  have rd1065₀ := evm_run rd1048 with [
    swap1, swap4, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap4, swap1, swap2, dup5, and, caller, sub]
  have rd1065 := rd1065₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd1065
  have hsub : UInt256.sub (solcSourceWord I) (governorReturnWord σ I) ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      exact hauth h.symm)
  have hsub' :
      UInt256.sub (UInt256.ofNat I.source.val) (UInt256.land solcAddrMask (governorWord σ I)) ≠
        ⟨0⟩ := by
    simpa [solcSourceWord, governorReturnWord, u256_land_comm solcAddrMask (governorWord σ I)]
      using hsub
  exact evm_run rd1065 with [
    push2 ⟨1622⟩, jumpiT hsub' (by native_decide),
    jumpdest, dup6,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨431085831⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferGovernorUnauthorizedSelector)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    caller, dup2, dup5, add,
    raw mstore 3 (transferGovernorUnauthorizedMem (solcSourceWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold transferGovernorUnauthorizedMem solcSourceWord
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, swap1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_auth_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1069⟩
      [setRewardConfigCometWord I, ⟨4⟩, ⟨224⟩, solcAddrMask,
        setRewardConfigTokenWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1044⟩ :=
    cometRewardsSetRewardConfigX_dec1044_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz68 hsize hhi hcanon0 hcanon1 hreach
  have rd1047 := evm_run rd1044 with [jumpdest, push1 ⟨0⟩]
  obtain ⟨_, _, rd1048₀⟩ := rd1047.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1048⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1048⟩
      [governorWord σ I, setRewardConfigTokenWord I, ⟨224⟩,
        setRewardConfigCometWord I, ⟨4⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd1048₀⟩
  have rd1065₀ := evm_run rd1048 with [
    swap1, swap4, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap4, swap1, swap2, dup5, and, caller, sub]
  have rd1065 := rd1065₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd1065
  have hsub :
      UInt256.sub (UInt256.ofNat I.source.val) (UInt256.land solcAddrMask (governorWord σ I)) =
        ⟨0⟩ := by
    have hgov :
        UInt256.land solcAddrMask (governorWord σ I) = UInt256.ofNat I.source.val := by
      simpa [governorReturnWord, solcSourceWord,
        u256_land_comm solcAddrMask (governorWord σ I)] using hauth
    rw [hgov]
    exact u256_sub_self _
  rw [hsub] at rd1065
  exact ⟨_, _, evm_run rd1065 with [push2 ⟨1622⟩, jumpiNT (by decide)]⟩

def setRewardConfigWrapperAlreadyConfiguredSelector : UInt256 :=
  UInt256.shiftLeft (⟨977536693⟩ : UInt256) ⟨224⟩

noncomputable def setRewardConfigWrapperAlreadyConfiguredSelectorMem (comet : UInt256) :
    ByteArray :=
  (UInt256.toByteArray setRewardConfigWrapperAlreadyConfiguredSelector).write 0
    (rewardConfigHashMem comet) 128 32

noncomputable def setRewardConfigWrapperAlreadyConfiguredMem (comet : UInt256) : ByteArray :=
  (UInt256.toByteArray comet).write 0
    (setRewardConfigWrapperAlreadyConfiguredSelectorMem comet) 132 32

set_option maxHeartbeats 10000000 in
theorem cometRewardsSetRewardConfigX_revert_configured
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land (solcSlotWord σ I (setRewardConfigSlotOf I)) solcAddrMask ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1069⟩ :=
    cometRewardsSetRewardConfigX_auth_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz68 hsize hhi hcanon0 hcanon1 hauth hreach
  have hcleanComet :
      UInt256.land (setRewardConfigCometWord I) solcAddrMask =
        setRewardConfigCometWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigCometWord, calldataWord] using hcanon0)
  have hcleanCometLeft :
      UInt256.land solcAddrMask (setRewardConfigCometWord I) =
        setRewardConfigCometWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigCometWord I)]
    exact hcleanComet
  have hslot := setRewardConfigSlotOf_eq_solc I hcanon0
  have hkeccak := rewardConfigKeccakSlot (setRewardConfigCometWord I)
  have rd1076₀ := evm_run rd1069 with [
    dup4, and, swap2, dup3, push1 ⟨0⟩,
    raw mstore 0 (wordAt0Mem (setRewardConfigCometWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [hcleanCometLeft]
        rfl)
      (by decide) (by evm_ov)]
  have rd1076 := rd1076₀
  rw [hcleanCometLeft] at rd1076
  have rd1089 := evm_run rd1076 with [
    push1 ⟨1⟩, swap4, push1 ⟨32⟩, swap1, dup6, dup3,
    raw mstore 0 (rewardConfigHashMem (setRewardConfigCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, dup9, push1 ⟨0⟩]
  have rd1090₀ := rd1089.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost hkeccak (by decide) (by evm_ov)
  have rd1090 := rd1090₀
  rw [← hslot] at rd1090
  obtain ⟨_, _, rd1091₀⟩ := rd1090.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1091⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1091⟩
      [solcSlotWord σ I (setRewardConfigSlotOf I), solcAddrMask, solcAddrMask, ⟨32⟩,
        ⟨224⟩, ⟨4⟩, setRewardConfigCometWord I, ⟨1⟩, setRewardConfigTokenWord I,
        ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord] using rd1091₀⟩
  have rd1092 := evm_run rd1091 with [and]
  have rd1599 := evm_run rd1092 with [
    push2 ⟨1599⟩, jumpiT htoken (by native_decide)]
  have rd1602 := evm_run rd1599 with [
    jumpdest, dup8,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (rewardConfigHashMem_mload64 (setRewardConfigCometWord I))
      (by decide) (by evm_ov)]
  have rd1612 := evm_run rd1602 with [
    push4 ⟨977536693⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6
      (setRewardConfigWrapperAlreadyConfiguredSelectorMem (setRewardConfigCometWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        unfold setRewardConfigWrapperAlreadyConfiguredSelectorMem
        rfl)
      (by decide) (by evm_ov)]
  have rd1618 := evm_run rd1612 with [
    dup1, dup6, add, dup7, swap1,
    raw mstore 3
      (setRewardConfigWrapperAlreadyConfiguredMem (setRewardConfigCometWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold setRewardConfigWrapperAlreadyConfiguredMem
        rfl)
      (by decide) (by evm_ov)]
  exact evm_run rd1618 with [
    push1 ⟨36⟩, swap1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 10000000 in
theorem cometRewardsSetRewardConfigX_configured_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land (solcSlotWord σ I (setRewardConfigSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1096⟩
      [solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩, setRewardConfigCometWord I, ⟨1⟩,
        setRewardConfigTokenWord I, ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1069⟩ :=
    cometRewardsSetRewardConfigX_auth_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz68 hsize hhi hcanon0 hcanon1 hauth hreach
  have hcleanComet :
      UInt256.land (setRewardConfigCometWord I) solcAddrMask =
        setRewardConfigCometWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigCometWord, calldataWord] using hcanon0)
  have hcleanCometLeft :
      UInt256.land solcAddrMask (setRewardConfigCometWord I) =
        setRewardConfigCometWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigCometWord I)]
    exact hcleanComet
  have hslot := setRewardConfigSlotOf_eq_solc I hcanon0
  have hkeccak := rewardConfigKeccakSlot (setRewardConfigCometWord I)
  have rd1076₀ := evm_run rd1069 with [
    dup4, and, swap2, dup3, push1 ⟨0⟩,
    raw mstore 0 (wordAt0Mem (setRewardConfigCometWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [hcleanCometLeft]
        rfl)
      (by decide) (by evm_ov)]
  have rd1076 := rd1076₀
  rw [hcleanCometLeft] at rd1076
  have rd1089 := evm_run rd1076 with [
    push1 ⟨1⟩, swap4, push1 ⟨32⟩, swap1, dup6, dup3,
    raw mstore 0 (rewardConfigHashMem (setRewardConfigCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, dup9, push1 ⟨0⟩]
  have rd1090₀ := rd1089.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost hkeccak (by decide) (by evm_ov)
  have rd1090 := rd1090₀
  rw [← hslot] at rd1090
  obtain ⟨_, _, rd1091₀⟩ := rd1090.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1091⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1091⟩
      [solcSlotWord σ I (setRewardConfigSlotOf I), solcAddrMask, solcAddrMask, ⟨32⟩,
        ⟨224⟩, ⟨4⟩, setRewardConfigCometWord I, ⟨1⟩, setRewardConfigTokenWord I,
        ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord] using rd1091₀⟩
  have rd1092 := evm_run rd1091 with [and]
  rw [htoken] at rd1092
  exact ⟨_, _, evm_run rd1092 with [push2 ⟨1599⟩, jumpiNT (by decide)]⟩

def setRewardConfigWrapperBaseAccrualScaleSelectorShifted : UInt256 :=
  UInt256.shiftLeft (⟨1359440587⟩ : UInt256) ⟨225⟩

noncomputable def setRewardConfigWrapperBaseAccrualScaleCalldataMem
    (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray setRewardConfigWrapperBaseAccrualScaleSelectorShifted).write 0
    (rewardConfigHashMem (setRewardConfigCometWord I)) 128 32

theorem setRewardConfigWrapperBaseAccrualScaleCalldataMem_read128_4
    (I : ExecutionEnv) :
    (setRewardConfigWrapperBaseAccrualScaleCalldataMem I).readWithPadding 128 4 =
      baseAccrualScaleSelector := by
  unfold setRewardConfigWrapperBaseAccrualScaleCalldataMem
  rw [toByteArray_write_read_window_of_gap
    (b := setRewardConfigWrapperBaseAccrualScaleSelectorShifted)
    (mem := rewardConfigHashMem (setRewardConfigCometWord I))
    (off := 128) (start := 0) (len := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))]
  native_decide

theorem setRewardConfigWrapperBaseAccrualScaleCalldataMem_encode (I : ExecutionEnv) :
    config.externalABI.encode? "baseAccrualScale" [] =
      some ((setRewardConfigWrapperBaseAccrualScaleCalldataMem I).readWithPadding 128 4) := by
  rw [setRewardConfigWrapperBaseAccrualScaleCalldataMem_read128_4]
  rfl

abbrev setRewardConfigWrapperBasePostCallTail (I : ExecutionEnv) : List UInt256 :=
  [setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
    setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]

abbrev setRewardConfigWrapperBasePostCallStack (z : Bool) (I : ExecutionEnv) :
    List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: setRewardConfigWrapperBasePostCallTail I

noncomputable abbrev setRewardConfigWrapperBasePostCallMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (setRewardConfigWrapperBaseAccrualScaleCalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev setRewardConfigWrapperBasePostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
      (⟨4⟩ : UInt256).toNat)
    (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

theorem setRewardConfigWrapperBaseTarget_eq_targetWord (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat) =
      AccountAddress.ofUInt256 (setRewardConfigCometWord I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat (setRewardConfigCometWord I).toNat).isLt

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_call_baseAccrualScale
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land (solcSlotWord σ I (setRewardConfigSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ gasArg k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1115⟩
      [gasArg, setRewardConfigCometWord I, ⟨128⟩, ⟨4⟩, ⟨128⟩, ⟨32⟩,
        setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1096⟩ :=
    cometRewardsSetRewardConfigX_configured_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz68 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd1108 := evm_run rd1096 with [
    dup8,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (rewardConfigHashMem_mload64 (setRewardConfigCometWord I))
      (by decide) (by evm_ov),
    push4 ⟨1359440587⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        unfold setRewardConfigWrapperBaseAccrualScaleCalldataMem
        rfl)
      (by decide) (by evm_ov)]
  have rd1114 := evm_run rd1108 with [
    swap7, dup3, dup9, dup7, dup2, dup10]
  obtain ⟨gasArg, rd1115⟩ := evm_run rd1114 with [gas]
  exact ⟨gasArg, _, _, by simpa using rd1115⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_call_baseAccrualScale_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ_evm I = solcSourceWord I)
    (htoken : UInt256.land (solcSlotWord σ_evm I (setRewardConfigSlotOf I)) solcAddrMask = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ cA' σ'_evm σ'_solm A'_solm z out k C,
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 []
        (z,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) false ∧
      accountMapEquiv σ'_evm σ'_solm ∧
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack z I)
        (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
        (cA', σ'_evm) k C ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd1115⟩ :=
    cometRewardsSetRewardConfigX_call_baseAccrualScale
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz68 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd1115Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1115⟩
        (gasArg :: setRewardConfigCometWord I :: ⟨128⟩ :: ⟨4⟩ ::
          ⟨128⟩ :: ⟨32⟩ :: setRewardConfigWrapperBasePostCallTail I)
        (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
        (UInt256.ofNat 5) ByteArray.empty (cA, σ_evm) k0 C0 := by
    simpa [setRewardConfigWrapperBasePostCallTail] using rd1115
  have hdecCall :
      decode cometRewardsBytecode (⟨1115⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  obtain ⟨cA', σ'_evm, z, out, A_in, callGas, k', C', hΘ, rd1116, _houtSize⟩ :=
    RD.solcStaticcall (t := setRewardConfigWrapperBasePostCallTail I) rd1115Call hdecCall
      hdepth (by simp [setRewardConfigWrapperBasePostCallTail])
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  have houtSmall : out.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cA)
      (gh := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks)
      (σ := σ_evm)
      (σ₀ := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256 (setRewardConfigCometWord I))
      (c := toExecute σ_evm (AccountAddress.ofUInt256 (setRewardConfigCometWord I)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (setRewardConfigWrapperBaseAccrualScaleCalldataMem I).readWithPadding 128 4)
      (e := I.depth + 1) (H := I.header) (w := false)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtSign : out.size < 2 ^ 255 := by omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe :
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
        1024 := by
    simpa [initState] using hdepthNeI
  have htgt := setRewardConfigWrapperBaseTarget_eq_targetWord I
  have hcd := setRewardConfigWrapperBaseAccrualScaleCalldataMem_encode I
  have hcallE :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
        "baseAccrualScale" 0 []
        (z,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          out) false := by
    refine callCoincides
      (cfg := config)
      (evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      (name := "baseAccrualScale") (args := [])
      (tgt := EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
      (targetWord := setRewardConfigCometWord I)
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
      (inOff := ⟨128⟩) (inSize := ⟨4⟩) (callPerm := false)
      hdepthNe htgt hcd ?_
    simpa [initState] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv hcallE hAccounts
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
    hcallSolm, hPostAccounts, by
      simpa [setRewardConfigWrapperBasePostCallStack, setRewardConfigWrapperBasePostCallTail,
        setRewardConfigWrapperBasePostCallMem, setRewardConfigWrapperBasePostCallAw] using rd1116,
    houtSign⟩

theorem setRewardConfigWrapperBaseAccrualScaleCalldataMem_read64 (I : ExecutionEnv) :
    (setRewardConfigWrapperBaseAccrualScaleCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setRewardConfigWrapperBaseAccrualScaleCalldataMem
  rw [toByteArray_write_read_below_of_gap
    (b := setRewardConfigWrapperBaseAccrualScaleSelectorShifted)
    (mem := rewardConfigHashMem (setRewardConfigCometWord I))
    (off := 128) (read := 64)
    (by have hsz := rewardConfigHashMem_size (setRewardConfigCometWord I); omega)
    (by norm_num)
    (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))]
  exact rewardConfigHashMem_read64 (setRewardConfigCometWord I)

theorem setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128
    (I : ExecutionEnv) :
    128 ≤ (setRewardConfigWrapperBaseAccrualScaleCalldataMem I).size := by
  unfold setRewardConfigWrapperBaseAccrualScaleCalldataMem
  have h160 :=
    toByteArray_write_size_ge_off_add32 setRewardConfigWrapperBaseAccrualScaleSelectorShifted
      (rewardConfigHashMem (setRewardConfigCometWord I)) 128
      (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))
  omega

theorem setRewardConfigWrapperBasePostCallMem_read64 (I : ExecutionEnv) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (setRewardConfigWrapperBasePostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  dsimp [setRewardConfigWrapperBasePostCallMem]
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigWrapperBaseAccrualScaleCalldataMem_read64 I
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
      exact setRewardConfigBasePostCallLen_le_out_size houtSize
    rw [write_read_below_gen_extend out
      (setRewardConfigWrapperBaseAccrualScaleCalldataMem I) 128
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat 64
      hlen hsrc (setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I)
      (by norm_num)]
    exact setRewardConfigWrapperBaseAccrualScaleCalldataMem_read64 I

theorem setRewardConfigWrapperBasePostCallMem_size_ge128 (I : ExecutionEnv)
    {out : ByteArray} (houtSize : out.size < UInt256.size) :
    128 ≤ (setRewardConfigWrapperBasePostCallMem I out).size := by
  dsimp [setRewardConfigWrapperBasePostCallMem]
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
      exact setRewardConfigBasePostCallLen_le_out_size houtSize
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let base := setRewardConfigWrapperBaseAccrualScaleCalldataMem I
    have hdest : 128 ≤ base.size :=
      setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I
    by_cases hin : 128 + len ≤ base.size
    · rw [write_eq_gen out base 128 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < 128 + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem setRewardConfigWrapperBasePostCallMem_mload64 (I : ExecutionEnv)
    {out : ByteArray} (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setRewardConfigWrapperBasePostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigWrapperBasePostCallAw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
          ((setRewardConfigWrapperBasePostCallMem I out).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  apply mloadFreePtrValue
  · exact lt_of_lt_of_le (by norm_num)
      (setRewardConfigWrapperBasePostCallMem_size_ge128 I houtSize)
  · native_decide
  · exact setRewardConfigWrapperBasePostCallMem_read64 I houtSize

theorem setRewardConfigWrapperBasePostCallMem_read128_of_size_ge (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (setRewardConfigWrapperBasePostCallMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold setRewardConfigWrapperBasePostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  exact write32_read_back out
    (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
    128 hout32 (by exact setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I)

theorem setRewardConfigWrapperBasePostCallMem_size_ge160 (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    160 ≤ (setRewardConfigWrapperBasePostCallMem I out).size := by
  unfold setRewardConfigWrapperBasePostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  rw [write32_eq out (setRewardConfigWrapperBaseAccrualScaleCalldataMem I) 128 hout32
    (by exact setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  have hbase := setRewardConfigWrapperBaseAccrualScaleCalldataMem_size_ge128 I
  omega

theorem setRewardConfigWrapperBasePostCallMem_mload128_haw :
    ¬ (⟨128⟩ : UInt256) ≥ setRewardConfigWrapperBasePostCallAw * ⟨32⟩ := by
  native_decide

theorem setRewardConfigWrapperBasePostCallMem_mload128_of_size_ge
    (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setRewardConfigWrapperBasePostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ setRewardConfigWrapperBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperBasePostCallMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigWrapperBasePostCallMem I out)
    (aw := setRewardConfigWrapperBasePostCallAw)
    (off := ⟨128⟩) (memSize := (setRewardConfigWrapperBasePostCallMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact lt_of_lt_of_le (by omega)
        (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize))
    setRewardConfigWrapperBasePostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        setRewardConfigWrapperBasePostCallMem_read128_of_size_ge I hout32 houtSize])

noncomputable abbrev setRewardConfigWrapperBasePostDecodeMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨160⟩ : UInt256)).write 0
    (setRewardConfigWrapperBasePostCallMem I out) 64 32

theorem setRewardConfigWrapperBasePostDecodeMem_read128_of_size_ge
    (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (setRewardConfigWrapperBasePostDecodeMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold setRewardConfigWrapperBasePostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨160⟩ : UInt256))
    (setRewardConfigWrapperBasePostCallMem I out) 64 128
    (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize))
    (by omega)
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize))]
  exact setRewardConfigWrapperBasePostCallMem_read128_of_size_ge I hout32 houtSize

theorem setRewardConfigWrapperBasePostDecodeMem_mload128_of_size_ge
    (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setRewardConfigWrapperBasePostDecodeMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ setRewardConfigWrapperBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperBasePostDecodeMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigWrapperBasePostDecodeMem I out)
    (aw := setRewardConfigWrapperBasePostCallAw)
    (off := ⟨128⟩) (memSize := (setRewardConfigWrapperBasePostDecodeMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      unfold setRewardConfigWrapperBasePostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨160⟩ : UInt256))
        (setRewardConfigWrapperBasePostCallMem I out) 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize))]
      simp
      have hsz := setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize
      omega)
    setRewardConfigWrapperBasePostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        setRewardConfigWrapperBasePostDecodeMem_read128_of_size_ge I hout32 houtSize])

theorem setRewardConfigWrapperBasePostDecodeMem_read64
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    (setRewardConfigWrapperBasePostDecodeMem I baseOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigWrapperBasePostDecodeMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize))]
  rw [show (UInt256.toByteArray (⟨160⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨160⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨160⟩ : UInt256)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem setRewardConfigWrapperBasePostDecodeMem_size_ge160
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    160 ≤ (setRewardConfigWrapperBasePostDecodeMem I baseOut).size := by
  unfold setRewardConfigWrapperBasePostDecodeMem
  exact le_trans (setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize)
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨160⟩ : UInt256))
      (setRewardConfigWrapperBasePostCallMem I baseOut) (by rw [toByteArray_size])
      (by
        have hbase := setRewardConfigWrapperBasePostCallMem_size_ge160 I hout32 houtSize
        omega))

theorem setRewardConfigWrapperBasePostDecodeMem_mload64
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setRewardConfigWrapperBasePostDecodeMem I baseOut).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigWrapperBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperBasePostDecodeMem I baseOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigWrapperBasePostCallAw)
    (v := ⟨160⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := setRewardConfigWrapperBasePostDecodeMem_size_ge160 I
        (baseOut := baseOut) hout32 houtSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact setRewardConfigWrapperBasePostDecodeMem_read64 I hout32 houtSize)

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_after_baseAccrualScale_failure
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack false I)
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1116 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩
      [⟨0⟩, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C := by
    simpa [setRewardConfigWrapperBasePostCallStack,
      setRewardConfigWrapperBasePostCallTail] using rd
  have rd1117 := RD.swap8 rd1116 (by native_decide) (by simp)
  have rd1588 := evm_run rd1117 with [
    dup9, iszero, push2 ⟨1588⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd1591 := evm_run rd1588 with [
    jumpdest, dup10,
    raw mload 0 ⟨128⟩ setRewardConfigWrapperBasePostCallAw (by native_decide)
      mem_cost (setRewardConfigWrapperBasePostCallMem_mload64 I houtSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have rd1595pre := evm_run rd1591 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    out.write 0 (setRewardConfigWrapperBasePostCallMem I out) 128 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigWrapperBasePostCallAw.toNat 128 rdsz.toNat)
  have rd1596 := RD.returndatacopy
    (Cₘ aw2 - Cₘ setRewardConfigWrapperBasePostCallAw) mem2 aw2 rd1595pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by rfl)
    (by rfl)
    (by simp)
  have rd1599 := evm_run rd1596 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 128 rdsz.toNat)) - Cₘ aw2)
    rd1599 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by simp)

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_baseAccrualScale_callDepthLimit
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land (solcSlotWord σ I (setRewardConfigSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨gasArg, k0, C0, rd1115⟩ :=
    cometRewardsSetRewardConfigX_call_baseAccrualScale
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz68 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd1115Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1115⟩
        (gasArg :: setRewardConfigCometWord I :: ⟨128⟩ :: ⟨4⟩ ::
          ⟨128⟩ :: ⟨32⟩ :: setRewardConfigWrapperBasePostCallTail I)
        (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
        (UInt256.ofNat 5) ByteArray.empty (cA, σ) k0 C0 := by
    simpa [setRewardConfigWrapperBasePostCallTail] using rd1115
  have hdecCall :
      decode cometRewardsBytecode (⟨1115⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  have hdepthInit :
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth = 1024 := by
    simpa [initState] using hdepth
  obtain ⟨k', C', rdPost₀⟩ :=
    RD.solcStaticcallDepthLimit (t := setRewardConfigWrapperBasePostCallTail I)
      rd1115Call hdecCall hdepthInit (by simp [setRewardConfigWrapperBasePostCallTail])
  have rdPost :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack false I)
        (setRewardConfigWrapperBasePostCallMem I ByteArray.empty)
        setRewardConfigWrapperBasePostCallAw ByteArray.empty (cA, σ) k' C' := by
    simpa [setRewardConfigWrapperBasePostCallStack, setRewardConfigWrapperBasePostCallTail,
      setRewardConfigWrapperBasePostCallMem, setRewardConfigWrapperBasePostCallAw] using rdPost₀
  exact cometRewardsSetRewardConfigX_after_baseAccrualScale_failure rdPost
    (by simp [UInt256.size])

noncomputable abbrev setRewardConfigWrapperBasePostShortDecodeMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray ((⟨128⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩))).write 0
      (setRewardConfigWrapperBasePostCallMem I out) 64 32

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_baseAccrualScale_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack true I)
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd1116 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩
      [⟨1⟩, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C := by
    simpa [setRewardConfigWrapperBasePostCallStack,
      setRewardConfigWrapperBasePostCallTail] using rd
  have rd1117 := RD.swap8 rd1116 (by native_decide) (by simp)
  have rd1125 := evm_run rd1117 with [
    dup9, iszero, push2 ⟨1588⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩]
  have rd1126 := rdSwap9 rd1125 (by native_decide) (by simp)
  have rd1555 := evm_run rd1126 with [
    push2 ⟨1555⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd1558 := evm_run rd1555 with [
    jumpdest, dup3, swap2]
  have rd1559 := rdSwap9 rd1558 (by native_decide) (by simp)
  have rd1568₀ := evm_run rd1559 with [
    pop, push2 ⟨1581⟩, swap1, dup5, returndatasize, dup7, gt]
  have rd1568 := rd1568₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd1568
  let rounded : UInt256 :=
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩)
  let ptr : UInt256 := (⟨128⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ out.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt houtSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 128 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨128⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨128⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd1568 with [
    push2 ⟨734⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨709⟩, jump (by jump_dest),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperBasePostShortDecodeMem I out)
      setRewardConfigWrapperBasePostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest)]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨128⟩ : UInt256) + rdsz) ⟨128⟩) ⟨32⟩ = ⟨1⟩ := by
    simpa [rdsz] using solcDecodeEndLenCheckShort_128_32 (len := out.size) hshort
  have rd3114₀ := evm_run rd3106 with [
    jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub, slt]
  have rd3114 := rd3114₀
  rw [hlenCheck] at rd3114
  have rd1004 := evm_run rd3114 with [
    push2 ⟨1004⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_baseAccrualScale_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack true I)
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hbase64 : ¬ (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := setRewardConfigBaseReturnWord out
  have hbase64' : ¬ baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have rd1116 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩
      [⟨1⟩, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C := by
    simpa [setRewardConfigWrapperBasePostCallStack,
      setRewardConfigWrapperBasePostCallTail] using rd
  have rd1117 := RD.swap8 rd1116 (by native_decide) (by simp)
  have rd1125 := evm_run rd1117 with [
    dup9, iszero, push2 ⟨1588⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩]
  have rd1126 := rdSwap9 rd1125 (by native_decide) (by simp)
  have rd1555 := evm_run rd1126 with [
    push2 ⟨1555⟩, jumpiT (by native_decide) (by jump_dest)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd1558 := evm_run rd1555 with [
    jumpdest, dup3, swap2]
  have rd1559 := rdSwap9 rd1558 (by native_decide) (by simp)
  have rd1568₀ := evm_run rd1559 with [
    pop, push2 ⟨1581⟩, swap1, dup5, returndatasize, dup7, gt]
  have rd1568 := rd1568₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd1568
  have rd3071 := evm_run rd1568 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperBasePostDecodeMem I out)
      setRewardConfigWrapperBasePostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperBasePostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord setRewardConfigWrapperBasePostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord, setRewardConfigBaseReturnWord] using
          setRewardConfigWrapperBasePostDecodeMem_mload128_of_size_ge I hout32 houtSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hnotClean : UInt256.land baseWord uint64Mask ≠ baseWord :=
    uint64Mask_not_clean hbase64'
  have hneq :
      baseWord ≠
        UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) := by
    intro hEq
    exact hnotClean (by simpa [uint64Mask] using hEq.symm)
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hneq
  have rd1004 := evm_run rd3129 with [
    push2 ⟨1004⟩, jumpiT hsub (by jump_dest)]
  exact evm_run rd1004 with [
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

abbrev setRewardConfigWrapperAfterBaseDecodeStack (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [solcAddrMask, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
    setRewardConfigCometWord I, ⟨1⟩, baseWord, ⟨64⟩, ⟨0⟩]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_baseAccrualScale_decode_ok
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩ (setRewardConfigWrapperBasePostCallStack true I)
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hbase64 : (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1130⟩
      (setRewardConfigWrapperAfterBaseDecodeStack (setRewardConfigBaseReturnWord out) I)
      (setRewardConfigWrapperBasePostDecodeMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k' C' := by
  let baseWord : UInt256 := setRewardConfigBaseReturnWord out
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have rd1116 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1116⟩
      [⟨1⟩, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBasePostCallMem I out) setRewardConfigWrapperBasePostCallAw out
      acc k C := by
    simpa [setRewardConfigWrapperBasePostCallStack,
      setRewardConfigWrapperBasePostCallTail] using rd
  have rd1117 := RD.swap8 rd1116 (by native_decide) (by simp)
  have rd1125 := evm_run rd1117 with [
    dup9, iszero, push2 ⟨1588⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩]
  have rd1126 := rdSwap9 rd1125 (by native_decide) (by simp)
  have rd1555 := evm_run rd1126 with [
    push2 ⟨1555⟩, jumpiT (by native_decide) (by jump_dest)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd1558 := evm_run rd1555 with [
    jumpdest, dup3, swap2]
  have rd1559 := rdSwap9 rd1558 (by native_decide) (by simp)
  have rd1568₀ := evm_run rd1559 with [
    pop, push2 ⟨1581⟩, swap1, dup5, returndatasize, dup7, gt]
  have rd1568 := rd1568₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd1568
  have rd3071 := evm_run rd1568 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperBasePostDecodeMem I out)
      setRewardConfigWrapperBasePostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperBasePostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord setRewardConfigWrapperBasePostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord, setRewardConfigBaseReturnWord] using
          setRewardConfigWrapperBasePostDecodeMem_mload128_of_size_ge I hout32 houtSize)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup2, and, dup2, sub]
  have hclean : UInt256.land baseWord uint64Mask = baseWord :=
    uint64Mask_clean hbase64'
  have hcleanExpanded :
      UInt256.land baseWord
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using hclean
  have hsub :
      UInt256.sub baseWord
        (UInt256.land baseWord
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hcleanExpanded]
    exact u256_sub_self baseWord
  have rd3129zero := rd3129
  rw [hsub] at rd3129zero
  have rd1581 := evm_run rd3129zero with [
    push2 ⟨1004⟩, jumpiNT (by native_decide), swap1, jump (by jump_dest)]
  have rd1582 := evm_run rd1581 with [jumpdest]
  have rd1583 := RD.swap8 rd1582 (by native_decide) (by simp)
  have rd1130 := evm_run rd1583 with [swap1, push2 ⟨1130⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [baseWord, setRewardConfigWrapperAfterBaseDecodeStack,
      setRewardConfigBaseReturnWord] using rd1130⟩

noncomputable def setRewardConfigWrapperDecimalsCalldataMem
    (I : ExecutionEnv) (baseOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray setRewardConfigDecimalsSelectorShifted).write 0
    (setRewardConfigWrapperBasePostDecodeMem I baseOut) 160 32

theorem setRewardConfigWrapperDecimalsCalldataMem_read160_4
    (I : ExecutionEnv) (baseOut : ByteArray) :
    (setRewardConfigWrapperDecimalsCalldataMem I baseOut).readWithPadding 160 4 =
      decimalsSelector := by
  unfold setRewardConfigWrapperDecimalsCalldataMem
  rw [toByteArray_write_read_window_of_gap
    (b := setRewardConfigDecimalsSelectorShifted)
    (mem := setRewardConfigWrapperBasePostDecodeMem I baseOut)
    (off := 160) (start := 0) (len := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))]
  native_decide

theorem setRewardConfigWrapperDecimalsCalldataMem_encode
    (I : ExecutionEnv) (baseOut : ByteArray) :
    config.externalABI.encode? "decimals" [] =
      some ((setRewardConfigWrapperDecimalsCalldataMem I baseOut).readWithPadding 160 4) := by
  rw [setRewardConfigWrapperDecimalsCalldataMem_read160_4]
  rfl

abbrev setRewardConfigWrapperDecimalsTargetWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (setRewardConfigTokenWord I)

theorem setRewardConfigWrapperDecimalsTarget_eq_targetWord (I : ExecutionEnv)
    (hcanon : (setRewardConfigTokenWord I).toNat < EVM.addressModulus) :
    EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat) =
      AccountAddress.ofUInt256 (setRewardConfigWrapperDecimalsTargetWord I) := by
  have hcleanLeft :
      UInt256.land (setRewardConfigTokenWord I) solcAddrMask =
        setRewardConfigTokenWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigTokenWord, calldataWord] using hcanon)
  have hclean :
      UInt256.land solcAddrMask (setRewardConfigTokenWord I) =
        setRewardConfigTokenWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigTokenWord I), hcleanLeft]
  rw [setRewardConfigWrapperDecimalsTargetWord, hclean,
    accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat).isLt

abbrev setRewardConfigWrapperDecimalsCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M setRewardConfigWrapperBasePostCallAw.toNat 160 32)

abbrev setRewardConfigWrapperDecimalsPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M setRewardConfigWrapperDecimalsCallAw.toNat 160 4) 160 32)

abbrev setRewardConfigWrapperDecimalsPostCallTail (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
    setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
    ⟨64⟩, ⟨0⟩]

abbrev setRewardConfigWrapperDecimalsPostCallStack (z : Bool) (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: setRewardConfigWrapperDecimalsPostCallTail baseWord I

noncomputable abbrev setRewardConfigWrapperDecimalsPostCallMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  decOut.write 0 (setRewardConfigWrapperDecimalsCalldataMem I baseOut) 160
    (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat

theorem setRewardConfigWrapperDecimalsCalldataMem_size_ge192
    (I : ExecutionEnv) (baseOut : ByteArray) :
    192 ≤ (setRewardConfigWrapperDecimalsCalldataMem I baseOut).size := by
  unfold setRewardConfigWrapperDecimalsCalldataMem
  exact toByteArray_write_size_ge_off_add32 setRewardConfigDecimalsSelectorShifted
    (setRewardConfigWrapperBasePostDecodeMem I baseOut) 160
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))

theorem setRewardConfigWrapperDecimalsCalldataMem_read64
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    (setRewardConfigWrapperDecimalsCalldataMem I baseOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigWrapperDecimalsCalldataMem
  rw [toByteArray_write_read_below_of_gap
    (b := setRewardConfigDecimalsSelectorShifted)
    (mem := setRewardConfigWrapperBasePostDecodeMem I baseOut)
    (off := 160) (read := 64)
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperBasePostDecodeMem_size_ge160 I hout32 houtSize))
    (by norm_num)
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))]
  exact setRewardConfigWrapperBasePostDecodeMem_read64 I hout32 houtSize

theorem setRewardConfigWrapperDecimalsPostCallMem_size_ge96
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (hdecSize : decOut.size < UInt256.size) :
    96 ≤ (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).size := by
  unfold setRewardConfigWrapperDecimalsPostCallMem
  have hbase := setRewardConfigWrapperDecimalsCalldataMem_size_ge192 I baseOut
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat ≤ decOut.size :=
    setRewardConfigBasePostCallLen_le_out_size hdecSize
  exact le_trans (by omega)
    (byteArray_write_size_ge_base_of_le decOut
      (setRewardConfigWrapperDecimalsCalldataMem I baseOut) hlen (by omega))

theorem setRewardConfigWrapperDecimalsPostCallMem_read64
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigWrapperDecimalsPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigWrapperDecimalsCalldataMem_read64 I hout32 houtSize
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat ≤ decOut.size :=
      setRewardConfigBasePostCallLen_le_out_size hdecSize
    rw [write_read_below_gen_extend decOut
      (setRewardConfigWrapperDecimalsCalldataMem I baseOut)
      160 (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat 64
      hlen hsrc (by
        have hbase := setRewardConfigWrapperDecimalsCalldataMem_size_ge192 I baseOut
        omega)
      (by norm_num)]
    exact setRewardConfigWrapperDecimalsCalldataMem_read64 I hout32 houtSize

theorem setRewardConfigWrapperDecimalsPostCallMem_mload64
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigWrapperDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigWrapperDecimalsPostCallAw)
    (v := ⟨160⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := setRewardConfigWrapperDecimalsPostCallMem_size_ge96 I
        (baseOut := baseOut) (decOut := decOut) hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact setRewardConfigWrapperDecimalsPostCallMem_read64 I hout32 houtSize hdecSize)

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_call_decimals
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut : ByteArray} {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1130⟩
      (setRewardConfigWrapperAfterBaseDecodeStack baseWord I)
      (setRewardConfigWrapperBasePostDecodeMem I baseOut) setRewardConfigWrapperBasePostCallAw
      baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    ∃ gasArg k' C', RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1153⟩
      [gasArg, setRewardConfigWrapperDecimalsTargetWord I, ⟨160⟩, ⟨4⟩, ⟨160⟩,
        ⟨32⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsCalldataMem I baseOut)
      setRewardConfigWrapperDecimalsCallAw baseOut acc k' C' := by
  have hcleanToken :
      UInt256.land solcAddrMask (setRewardConfigTokenWord I) =
        setRewardConfigWrapperDecimalsTargetWord I := by
    rfl
  have rd1130 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1130⟩
      [solcAddrMask, setRewardConfigTokenWord I, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, baseWord, ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperBasePostDecodeMem I baseOut) setRewardConfigWrapperBasePostCallAw
      baseOut acc k C := by
    simpa [setRewardConfigWrapperAfterBaseDecodeStack] using rd
  have rd1135₀ := evm_run rd1130 with [
    jumpdest, pop, dup2, and, swap7]
  have rd1135 := rd1135₀
  rw [hcleanToken] at rd1135
  have rd1147 := evm_run rd1135 with [
    dup9,
    raw mload 0 ⟨160⟩ setRewardConfigWrapperBasePostCallAw (by native_decide)
      mem_cost (setRewardConfigWrapperBasePostDecodeMem_mload64 I hout32 houtSize)
      (by native_decide) (by evm_ov),
    push4 ⟨826074471⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 (setRewardConfigWrapperDecimalsCalldataMem I baseOut)
      setRewardConfigWrapperDecimalsCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
        unfold setRewardConfigWrapperDecimalsCalldataMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd1152 := evm_run rd1147 with [
    dup4, dup2, dup8, dup2, dup13]
  obtain ⟨gasArg, rd1153⟩ := evm_run rd1152 with [gas]
  exact ⟨gasArg, _, _, by simpa using rd1153⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_call_decimals_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {baseOut : ByteArray} {baseWord : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm σ'_solm : AccountMap}
    {A'_solm : Substate} {k C : ℕ}
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth.val < 1024)
    (hPostAccounts : accountMapEquiv σ'_evm σ'_solm)
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨1130⟩
      (setRewardConfigWrapperAfterBaseDecodeStack baseWord I)
      (setRewardConfigWrapperBasePostDecodeMem I baseOut) setRewardConfigWrapperBasePostCallAw
      baseOut (cA', σ'_evm) k C)
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    ∃ cA'' σ''_evm σ''_solm A''_solm z out k' C',
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 []
        (z,
          { { initState cA gh bl σ_solm σ₀ g A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' } with
              accountMap := σ''_solm
              substate := A''_solm
              createdAccounts := cA'' },
          out) false ∧
      accountMapEquiv σ''_evm σ''_solm ∧
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨1154⟩
        (setRewardConfigWrapperDecimalsPostCallStack z baseWord I)
        (setRewardConfigWrapperDecimalsPostCallMem I baseOut out)
        setRewardConfigWrapperDecimalsPostCallAw out (cA'', σ''_evm) k' C' ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd1153⟩ :=
    cometRewardsSetRewardConfigX_call_decimals (rd := rd) hout32 houtSize
  have rd1153Call :
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨1153⟩
        (gasArg :: setRewardConfigWrapperDecimalsTargetWord I :: ⟨160⟩ :: ⟨4⟩ ::
          ⟨160⟩ :: ⟨32⟩ :: setRewardConfigWrapperDecimalsPostCallTail baseWord I)
        (setRewardConfigWrapperDecimalsCalldataMem I baseOut)
        setRewardConfigWrapperDecimalsCallAw baseOut (cA', σ'_evm) k0 C0 := by
    simpa [setRewardConfigWrapperDecimalsPostCallTail] using rd1153
  have hdecCall :
      decode cometRewardsBytecode (⟨1153⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  obtain ⟨cA'', σ''_evm, z, out, A_in, callGas, k', C', hΘ, rd1154, _houtSize⟩ :=
    RD.solcStaticcall (t := setRewardConfigWrapperDecimalsPostCallTail baseWord I)
      rd1153Call hdecCall hdepth (by simp [setRewardConfigWrapperDecimalsPostCallTail])
  obtain ⟨g'', A''_evm, hΘeq⟩ := hΘ
  let evmEBase : EVM.State :=
    { initState cA gh bl σ_evm σ₀ g A I with
        accountMap := σ'_evm
        substate := A'_solm
        createdAccounts := cA' }
  let evmSBase : EVM.State :=
    { initState cA gh bl σ_solm σ₀ g A I with
        accountMap := σ'_solm
        substate := A'_solm
        createdAccounts := cA' }
  have houtSmall : out.size < 2 ^ 138 := by
    exact Theta_returnData_size_lt_2pow138_of_eq
      (blob := I.blobVersionedHashes) (cA := cA')
      (gh := (initState cA gh bl σ_evm σ₀ g A I).genesisBlockHeader)
      (blocks := (initState cA gh bl σ_evm σ₀ g A I).blocks)
      (σ := σ'_evm)
      (σ₀ := (initState cA gh bl σ_evm σ₀ g A I).σ₀)
      (A := A_in)
      (s := AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner))
      (o := I.sender)
      (r := AccountAddress.ofUInt256 (setRewardConfigWrapperDecimalsTargetWord I))
      (c := toExecute σ'_evm
        (AccountAddress.ofUInt256 (setRewardConfigWrapperDecimalsTargetWord I)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (setRewardConfigWrapperDecimalsCalldataMem I baseOut).readWithPadding 160 4)
      (e := I.depth + 1) (H := I.header) (w := false)
      hΘeq
      (by exact Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256 _ _ _)
  have houtSign : out.size < 2 ^ 255 := by omega
  have hdepthNeI : I.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepth
    exact absurd hdepth (by decide)
  have hdepthNe : evmEBase.executionEnv.depth ≠ 1024 := by
    simpa [evmEBase, initState] using hdepthNeI
  have htgt := setRewardConfigWrapperDecimalsTarget_eq_targetWord I hcanon1
  have hcd := setRewardConfigWrapperDecimalsCalldataMem_encode I baseOut
  have hcallE :
      typedCallViaEVM config evmEBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
        "decimals" 0 []
        (z,
          { evmEBase with
              accountMap := σ''_evm
              substate := A''_evm
              createdAccounts := cA'' },
          out) false := by
    refine callCoincides
      (cfg := config) (evm := evmEBase)
      (name := "decimals") (args := [])
      (tgt := EVM.address (AccountAddress.ofNat (setRewardConfigTokenWord I).toNat))
      (targetWord := setRewardConfigWrapperDecimalsTargetWord I)
      (cA' := cA'') (σ' := σ''_evm) (A' := A''_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := setRewardConfigWrapperDecimalsCalldataMem I baseOut)
      (inOff := ⟨160⟩) (inSize := ⟨4⟩) (callPerm := false)
      hdepthNe htgt hcd ?_
    simpa [evmEBase, initState] using hΘeq
  obtain ⟨σ''_solm, A''_solm, hcallSolm, hPostAccounts'⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmSBase) hcallE
      (by simpa [evmEBase, evmSBase, initState] using hPostAccounts)
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase, initState])
      (by simp [evmEBase, evmSBase])
      (by simp [evmEBase, evmSBase, initState])
  exact ⟨cA'', σ''_evm, σ''_solm, A''_solm, z, out, k', C',
    by
      simpa [evmSBase, initState] using hcallSolm,
    hPostAccounts',
    by
      simpa [setRewardConfigWrapperDecimalsPostCallStack,
        setRewardConfigWrapperDecimalsPostCallTail, setRewardConfigWrapperDecimalsPostCallMem,
        setRewardConfigWrapperDecimalsPostCallAw] using rd1154,
    houtSign⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_failure
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack false baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hbase32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨0⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd741 := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd744 := evm_run rd741 with [
    jumpdest, dup11,
    raw mload 0 ⟨160⟩ setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigWrapperDecimalsPostCallMem_mload64 I hbase32 hbaseSize hdecSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have rd748pre := evm_run rd744 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    decOut.write 0 (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 160 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigWrapperDecimalsPostCallAw.toNat 160 rdsz.toNat)
  have rd748 := RD.returndatacopy
    (Cₘ aw2 - Cₘ setRewardConfigWrapperDecimalsPostCallAw) mem2 aw2 rd748pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      rw [show (⟨160⟩ : UInt256).toNat = 160 from rfl])
    (by rfl)
    (by rfl)
    (by simp)
  have rd751 := evm_run rd748 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 160 rdsz.toNat)) - Cₘ aw2)
    rd751 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      rw [show (⟨160⟩ : UInt256).toNat = 160 from rfl])
    (by simp)

noncomputable abbrev setRewardConfigWrapperDecimalsPostShortDecodeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray ((⟨160⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat decOut.size + ⟨31⟩))).write 0
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 64 32

noncomputable abbrev setRewardConfigWrapperDecimalsPostDecodeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0
    (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 64 32

theorem setRewardConfigWrapperDecimalsPostCallMem_read160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).readWithPadding 160 32 =
      decOut.extract 0 32 := by
  unfold setRewardConfigWrapperDecimalsPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := decOut.size)
      (by decide) hdec32 hdecSize
  rw [hlen]
  rw [write32_read_back decOut (setRewardConfigWrapperDecimalsCalldataMem I baseOut) 160
    (by exact hdec32)
    (by
      have hbase := setRewardConfigWrapperDecimalsCalldataMem_size_ge192 I baseOut
      omega)]

theorem setRewardConfigWrapperDecimalsPostCallMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut).size := by
  unfold setRewardConfigWrapperDecimalsPostCallMem
  have hbase := setRewardConfigWrapperDecimalsCalldataMem_size_ge192 I baseOut
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := decOut.size)
      (by decide) hdec32 hdecSize
  rw [hlen]
  exact le_trans hbase
    (byteArray_write_size_ge_base_of_le decOut
      (setRewardConfigWrapperDecimalsCalldataMem I baseOut) hdec32 (by omega))

theorem setRewardConfigWrapperDecimalsPostDecodeMem_read160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).readWithPadding 160 32 =
      decOut.extract 0 32 := by
  unfold setRewardConfigWrapperDecimalsPostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨192⟩ : UInt256))
    (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 64 160
    (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
          hdec32 hdecSize))
    (by omega)
    (by
      exact le_trans (by omega)
        (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
          hdec32 hdecSize))]
  exact setRewardConfigWrapperDecimalsPostCallMem_read160_of_size_ge I hdec32 hdecSize

theorem setRewardConfigWrapperDecimalsPostDecodeMem_mload160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).size
        ∨ (⟨160⟩ : UInt256) ≥ setRewardConfigWrapperDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (decOut.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
    (aw := setRewardConfigWrapperDecimalsPostCallAw)
    (off := ⟨160⟩)
    (memSize := (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).size)
    rfl
    (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
      unfold setRewardConfigWrapperDecimalsPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨192⟩ : UInt256))
        (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 64
        (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      simp
      have hsz := setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
        hdec32 hdecSize
      omega)
    (by native_decide)
    |>.trans (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
        setRewardConfigWrapperDecimalsPostDecodeMem_read160_of_size_ge I hdec32 hdecSize])

theorem setRewardConfigWrapperDecimalsPostDecodeMem_mload64_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigWrapperDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨192⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigWrapperDecimalsPostCallAw) (v := ⟨192⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigWrapperDecimalsPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨192⟩ : UInt256))
        (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) 64
        (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      simp
      have hsz := setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
        hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigWrapperDecimalsPostDecodeMem
      rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      rw [show (UInt256.toByteArray (⟨192⟩ : UInt256)).extract 0 32 =
          UInt256.toByteArray (⟨192⟩ : UInt256) by
        rw [show 32 = (UInt256.toByteArray (⟨192⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact byteArray_extract_self _])

theorem setRewardConfigWrapperDecimalsPostDecodeMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut).size := by
  unfold setRewardConfigWrapperDecimalsPostDecodeMem
  exact le_trans
    (setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
      hdec32 hdecSize)
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨192⟩ : UInt256))
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut) (by rw [toByteArray_size])
      (by
        have hbase :=
          setRewardConfigWrapperDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
            hdec32 hdecSize
        omega))

noncomputable def setRewardConfigWrapperSuccessFreeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
    64 ⟨320⟩

noncomputable def setRewardConfigWrapperSuccessTokenMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigWrapperSuccessFreeMem I baseOut decOut) 192
    (setRewardConfigWrapperDecimalsTargetWord I)

noncomputable def setRewardConfigWrapperSuccessRescaleMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigWrapperSuccessTokenMem I baseOut decOut) 224 rescale

noncomputable def setRewardConfigWrapperSuccessBitMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigWrapperSuccessRescaleMem I baseOut decOut rescale)
    256 bit

noncomputable def setRewardConfigWrapperSuccessMultiplierMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigWrapperSuccessBitMem I baseOut decOut rescale bit)
    288 setRewardConfigMultiplierWord

noncomputable def setRewardConfigWrapperSuccessCometMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (setRewardConfigWrapperSuccessMultiplierMem I baseOut decOut rescale bit)
    0 (setRewardConfigCometWord I)

noncomputable def setRewardConfigWrapperSuccessArgsMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (setRewardConfigWrapperSuccessCometMem I baseOut decOut rescale bit) 32 ⟨1⟩

theorem setRewardConfigWrapperSuccessFreeMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigWrapperSuccessFreeMem I baseOut decOut).size := by
  unfold setRewardConfigWrapperSuccessFreeMem Reasoning.Theory.writeWord
  have hbase := setRewardConfigWrapperDecimalsPostDecodeMem_size_ge192 I (baseOut := baseOut)
    hdec32 hdecSize
  exact le_trans hbase
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨320⟩ : UInt256))
      (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
      (by rw [toByteArray_size]) (by omega))

theorem setRewardConfigWrapperSuccessTokenMem_size_ge224
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    224 ≤ (setRewardConfigWrapperSuccessTokenMem I baseOut decOut).size := by
  have hfree := setRewardConfigWrapperSuccessFreeMem_size_ge192 I (baseOut := baseOut)
    hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessTokenMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num))

theorem setRewardConfigWrapperSuccessRescaleMem_size_ge256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    256 ≤ (setRewardConfigWrapperSuccessRescaleMem I baseOut decOut rescale).size := by
  have htoken := setRewardConfigWrapperSuccessTokenMem_size_ge224 I (baseOut := baseOut)
    hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessRescaleMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))

theorem setRewardConfigWrapperSuccessBitMem_size_ge288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    288 ≤ (setRewardConfigWrapperSuccessBitMem I baseOut decOut rescale bit).size := by
  have hrescale := setRewardConfigWrapperSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessBitMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))

theorem setRewardConfigWrapperSuccessMultiplierMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigWrapperSuccessMultiplierMem I baseOut decOut rescale bit).size := by
  have hbit := setRewardConfigWrapperSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessMultiplierMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))

theorem setRewardConfigWrapperSuccessCometMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigWrapperSuccessCometMem I baseOut decOut rescale bit).size := by
  unfold setRewardConfigWrapperSuccessCometMem
  rw [writeWord_size]
  · have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))

theorem setRewardConfigWrapperSuccessArgsMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size := by
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_size]
  · have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))

theorem setRewardConfigWrapperSuccessArgsMem_read0
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 0 32 =
      UInt256.toByteArray (setRewardConfigCometWord I) := by
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessCometMem
    rw [writeWord_read_back]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · left
    have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_read32
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_back]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))

theorem setRewardConfigWrapperSuccessArgsMem_read0_64
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 0 64 =
      UInt256.toByteArray (setRewardConfigCometWord I) ++
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split _ 0 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [setRewardConfigWrapperSuccessArgsMem_read0 I rescale bit hdec32 hdecSize,
      setRewardConfigWrapperSuccessArgsMem_read32 I rescale bit hdec32 hdecSize]
  · have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega

theorem setRewardConfigWrapperSuccessArgsMem_keccakSlot
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
            0 64))) =
      solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I) := by
  rw [setRewardConfigWrapperSuccessArgsMem_read0_64 I baseOut decOut rescale bit
    hdec32 hdecSize]
  unfold solcMappingSlot
  exact mappingSlot_single (setRewardConfigCometWord I) ⟨1⟩

theorem setRewardConfigWrapperSuccessArgsMem_read64
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold setRewardConfigWrapperSuccessArgsMem setRewardConfigWrapperSuccessCometMem
  rw [writeWord_read_preserved, writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessMultiplierMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigWrapperSuccessBitMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigWrapperSuccessRescaleMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigWrapperSuccessTokenMem
          rw [writeWord_read_preserved]
          · unfold setRewardConfigWrapperSuccessFreeMem
            rw [writeWord_read_back]
            exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num))
          · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num))
          · left
            have hfree := setRewardConfigWrapperSuccessFreeMem_size_ge192 I
              (baseOut := baseOut) hdec32 hdecSize
            constructor <;> omega
        · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))
        · left
          have htoken := setRewardConfigWrapperSuccessTokenMem_size_ge224 I
            (baseOut := baseOut) hdec32 hdecSize
          constructor <;> omega
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
      · left
        have hrescale := setRewardConfigWrapperSuccessRescaleMem_size_ge256 I
          (baseOut := baseOut) rescale hdec32 hdecSize
        constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
    · left
      have hbit := setRewardConfigWrapperSuccessBitMem_size_ge288 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
  · right
    have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right
    have hcomet :
        320 ≤ (Reasoning.Theory.writeWord
          (setRewardConfigWrapperSuccessMultiplierMem I baseOut decOut rescale bit) 0
          (setRewardConfigCometWord I)).size := by
      simpa [setRewardConfigWrapperSuccessCometMem] using
        setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
          rescale bit hdec32 hdecSize
    constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_mload64
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨64⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨320⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := ⟨320⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact setRewardConfigWrapperSuccessArgsMem_read64 I rescale bit hdec32 hdecSize)

theorem setRewardConfigWrapperSuccessArgsMem_read192
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 192 32 =
      UInt256.toByteArray (setRewardConfigWrapperDecimalsTargetWord I) := by
  have htoken := setRewardConfigWrapperSuccessTokenMem_size_ge224 I (baseOut := baseOut)
    hdec32 hdecSize
  have hrescale := setRewardConfigWrapperSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  have hbit := setRewardConfigWrapperSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigWrapperSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigWrapperSuccessBitMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigWrapperSuccessRescaleMem
          rw [writeWord_read_preserved]
          · unfold setRewardConfigWrapperSuccessTokenMem
            rw [writeWord_read_back]
            exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num))
          · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))
          · left; constructor <;> omega
        · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
        · left; constructor <;> omega
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
      · left; constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_read224
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 224 32 =
      UInt256.toByteArray rescale := by
  have hrescale := setRewardConfigWrapperSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  have hbit := setRewardConfigWrapperSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigWrapperSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigWrapperSuccessBitMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigWrapperSuccessRescaleMem
          rw [writeWord_read_back]
          exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))
        · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
        · left; constructor <;> omega
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
      · left; constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_read256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 256 32 =
      UInt256.toByteArray bit := by
  have hbit := setRewardConfigWrapperSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigWrapperSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigWrapperSuccessBitMem
        rw [writeWord_read_back]
        exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
      · left; constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_read288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 288 32 =
      UInt256.toByteArray setRewardConfigMultiplierWord := by
  have hmul := setRewardConfigWrapperSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigWrapperSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigWrapperSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigWrapperSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigWrapperSuccessMultiplierMem
      rw [writeWord_read_back]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigWrapperSuccessArgsMem_mload192
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨192⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨192⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨192⟩ : UInt256).toNat 32))) =
      setRewardConfigWrapperDecimalsTargetWord I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨192⟩ : UInt256)) (aw := (⟨10⟩ : UInt256))
    (v := setRewardConfigWrapperDecimalsTargetWord I)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      exact setRewardConfigWrapperSuccessArgsMem_read192 I rescale bit hdec32 hdecSize)

theorem setRewardConfigWrapperSuccessArgsMem_mload224
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨224⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨224⟩ : UInt256).toNat 32))) = rescale := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨224⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := rescale)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      exact setRewardConfigWrapperSuccessArgsMem_read224 I rescale bit hdec32 hdecSize)

theorem setRewardConfigWrapperSuccessArgsMem_mload256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨256⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) = bit := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := bit)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      exact setRewardConfigWrapperSuccessArgsMem_read256 I rescale bit hdec32 hdecSize)

theorem setRewardConfigWrapperSuccessArgsMem_mload288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨288⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) = setRewardConfigMultiplierWord := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨288⟩ : UInt256)) (aw := (⟨10⟩ : UInt256))
    (v := setRewardConfigMultiplierWord)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      have hsize := setRewardConfigWrapperSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      exact setRewardConfigWrapperSuccessArgsMem_read288 I rescale bit hdec32 hdecSize)

set_option maxHeartbeats 1000000 in
private theorem setRewardConfigWrapperSlot0RuntimeBase_toNat
    (old token rescale : UInt256) :
    (UInt256.lor
      (UInt256.lor
        (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) old)
        (UInt256.land token solcAddrMask))
      (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))).toNat =
      token.toNat % 2 ^ 160 + 2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 232 * (old.toNat / 2 ^ 232) := by
  let low : Nat := token.toNat % 2 ^ 160
  let mid : Nat := rescale.toNat % 2 ^ 64
  let high : Nat := old.toNat / 2 ^ 232
  have hlow : low < 2 ^ 160 := by
    exact Nat.mod_lt _ (by norm_num)
  have hmid : mid < 2 ^ 64 := by
    exact Nat.mod_lt _ (by norm_num)
  have hhigh : high < 2 ^ 24 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have hpackedLt :
      low + 2 ^ 160 * mid + 2 ^ 232 * high < UInt256.size := by
    have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hmidle : mid ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt hmid
    have hhighle : high ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hhigh
    have hmidterm : 2 ^ 160 * mid ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ hmidle
    have hhiterm : 2 ^ 232 * high ≤ 2 ^ 232 * (2 ^ 24 - 1) :=
      Nat.mul_le_mul_left _ hhighle
    have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) +
        2 ^ 232 * (2 ^ 24 - 1) < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have htokenLow :
      (UInt256.land token solcAddrMask).toNat = low := by
    rw [u256_land_toNat]
    have hmask : solcAddrMask.toNat = 2 ^ 160 - 1 := by
      native_decide
    rw [hmask, nat_land_mask_eq_mod]
    have hlt : token.toNat % 2 ^ 160 < UInt256.size := by
      have h := Nat.mod_lt token.toNat (by norm_num : 0 < 2 ^ 160)
      norm_num [UInt256.size] at h ⊢
      omega
    rw [Nat.mod_eq_of_lt hlt]
  have hOldHigh :
      (((⟨0xffffff⟩ : UInt256).shiftLeft ⟨232⟩).land old).toNat =
        high * 2 ^ 232 := by
    rw [u256_land_toNat]
    have hmask : (((⟨0xffffff⟩ : UInt256).shiftLeft ⟨232⟩).toNat) =
        2 ^ 256 - 2 ^ 232 := by
      native_decide
    rw [hmask]
    rw [nat_land_comm]
    rw [natLandClearLow old.toNat 232 (by norm_num) (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)]
    have hlt : old.toNat / 2 ^ 232 * 2 ^ 232 < UInt256.size :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
    rw [Nat.mod_eq_of_lt hlt]
  have hlowHigh :
      ((((⟨0xffffff⟩ : UInt256).shiftLeft ⟨232⟩).land old).lor
          (token.land solcAddrMask)).toNat =
        low + high * 2 ^ 232 := by
    rw [u256_lor_toNat, hOldHigh, htokenLow]
    rw [nat_lor_comm]
    rw [nat_lor_shift_add low high 232
      (lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by norm_num) (by norm_num)))]
    have hlt : low + high * 2 ^ 232 < UInt256.size := by
      have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
      have hhighle : high ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hhigh
      have hhiterm : high * 2 ^ 232 ≤ (2 ^ 24 - 1) * 2 ^ 232 :=
        Nat.mul_le_mul_right _ hhighle
      have hmax : (2 ^ 160 - 1) + (2 ^ 24 - 1) * 2 ^ 232 < UInt256.size := by
        norm_num [UInt256.size, Nat.pow_add]
      omega
    rw [Nat.mod_eq_of_lt hlt]
  have hmidWord :
      ((rescale.shiftLeft ⟨160⟩).land
          (((⟨1⟩ : UInt256).shiftLeft ⟨224⟩).sub
            ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩))).toNat =
        mid * 2 ^ 160 := by
    rw [u256_land_toNat]
    have hmask :
        ((((⟨1⟩ : UInt256).shiftLeft ⟨224⟩).sub
            ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩)).toNat) =
          (2 : Nat) ^ 224 - 2 ^ 160 := by
      native_decide
    have hshift :
        (rescale.shiftLeft ⟨160⟩).toNat =
          (rescale.toNat <<< 160) % 2 ^ 256 := by
      unfold UInt256.shiftLeft UInt256.toNat
      show (Fin.shiftLeft rescale.val (⟨160⟩ : UInt256).val).val = _
      unfold Fin.shiftLeft
      rw [show (⟨160⟩ : UInt256).val = 160 by rfl]
      change (rescale.toNat <<< 160) % UInt256.size =
        (rescale.toNat <<< 160) % 2 ^ 256
      norm_num [UInt256.size]
    rw [hshift, hmask, setRewardConfigNatLandShiftLeft160_mid64]
    have hlt : mid * 2 ^ 160 < UInt256.size := by
      calc
        mid * 2 ^ 160 < 2 ^ 64 * 2 ^ 160 :=
          Nat.mul_lt_mul_of_pos_right hmid (by norm_num)
        _ = 2 ^ 224 := by rw [← Nat.pow_add]
        _ < UInt256.size := by norm_num [UInt256.size]
    rw [Nat.mod_eq_of_lt hlt]
  rw [u256_lor_toNat, hlowHigh, hmidWord]
  have hlor :
      Nat.lor (low + high * 2 ^ 232) (mid * 2 ^ 160) =
        low + mid * 2 ^ 160 + high * 2 ^ 232 := by
    rw [show high * 2 ^ 232 = (high * 2 ^ 8) * 2 ^ 224 by ring]
    exact setRewardConfigNatLorPacked160_224 low mid (high * 2 ^ 8) hlow hmid
  rw [hlor]
  rw [show low + mid * 2 ^ 160 + high * 2 ^ 232 =
      low + 2 ^ 160 * mid + 2 ^ 232 * high by ring]
  exact Nat.mod_eq_of_lt hpackedLt

private theorem setRewardConfigWrapperSlot0Down_bytecodeExpr_runtime
    (old token rescale : UInt256) :
    UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) old)
          (UInt256.land token solcAddrMask))
        (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
      (UInt256.land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)
        (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)) =
      setRewardConfigSlot0Down old token rescale := by
  apply u256_inj
  have hprefix :
      UInt256.land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)
        (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩) = (⟨0⟩ : UInt256) := by
    native_decide
  rw [hprefix, u256_lor_zero, setRewardConfigSlot0Down_toNat]
  exact setRewardConfigWrapperSlot0RuntimeBase_toNat old token rescale

set_option maxHeartbeats 1000000 in
private theorem setRewardConfigWrapperSlot0Up_bytecodeExpr_runtime_toNat
    (old token rescale : UInt256) :
    (UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) old)
          (UInt256.land token solcAddrMask))
        (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
      (UInt256.land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)
        (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩))).toNat =
      token.toNat % 2 ^ 160 + 2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 + 2 ^ 232 * (old.toNat / 2 ^ 232) := by
  let low : Nat := token.toNat % 2 ^ 160
  let mid : Nat := rescale.toNat % 2 ^ 64
  let high : Nat := old.toNat / 2 ^ 232
  have hlow : low < 2 ^ 160 := by
    exact Nat.mod_lt _ (by norm_num)
  have hmid : mid < 2 ^ 64 := by
    exact Nat.mod_lt _ (by norm_num)
  have hhigh : high < 2 ^ 24 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have hlow224 : low + 2 ^ 160 * mid < 2 ^ 224 := by
    have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hmidle : mid ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt hmid
    have hmidterm : 2 ^ 160 * mid ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ hmidle
    have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) < 2 ^ 224 := by
      norm_num [Nat.pow_add]
    omega
  have hfinalLt :
      low + 2 ^ 160 * mid + 2 ^ 224 + 2 ^ 232 * high < UInt256.size := by
    have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hmidle : mid ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt hmid
    have hhighle : high ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hhigh
    have hmidterm : 2 ^ 160 * mid ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ hmidle
    have hhiterm : 2 ^ 232 * high ≤ 2 ^ 232 * (2 ^ 24 - 1) :=
      Nat.mul_le_mul_left _ hhighle
    have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) + 2 ^ 224 +
        2 ^ 232 * (2 ^ 24 - 1) < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hbase :
      (UInt256.lor
        (UInt256.lor
          (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) old)
          (UInt256.land token solcAddrMask))
        (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))).toNat =
        low + 2 ^ 160 * mid + 2 ^ 232 * high := by
    simpa [low, mid, high] using
      setRewardConfigWrapperSlot0RuntimeBase_toNat old token rescale
  have hprefix :
      (UInt256.land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)
        (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)).toNat = 2 ^ 224 := by
    native_decide
  rw [u256_lor_toNat, hbase, hprefix]
  have hlor :
      Nat.lor (low + 2 ^ 160 * mid + 2 ^ 232 * high) (2 ^ 224) =
        low + 2 ^ 160 * mid + 2 ^ 224 + 2 ^ 232 * high := by
    rw [show low + 2 ^ 160 * mid + 2 ^ 232 * high =
        (low + 2 ^ 160 * mid) + high * 2 ^ 232 by ring]
    rw [show (2 : Nat) ^ 224 = 1 * 2 ^ 224 by ring]
    rw [setRewardConfigNatLorPacked224_232 (low + 2 ^ 160 * mid) 1 high
      hlow224 (by norm_num)]
    ring
  rw [hlor, Nat.mod_eq_of_lt hfinalLt]

private theorem setRewardConfigWrapperSlot0Up_bytecodeExpr_runtime
    (old token rescale : UInt256) :
    UInt256.lor
      (UInt256.lor
        (UInt256.lor
          (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) old)
          (UInt256.land token solcAddrMask))
        (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
      (UInt256.land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)
        (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)) =
      setRewardConfigSlot0Up old token rescale := by
  apply u256_inj
  rw [setRewardConfigWrapperSlot0Up_bytecodeExpr_runtime_toNat,
    setRewardConfigSlot0Up_toNat]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hshort : decOut.size < 32)
    (hdecSize : decOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨1⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd1506₀ := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨1499⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup5, dup2, dup2, returndatasize, dup4, gt]
  have rd1506 := rd1506₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd1506
  let rounded : UInt256 :=
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat decOut.size + ⟨31⟩)
  let ptr : UInt256 := (⟨160⟩ : UInt256) + rounded
  have hroundedLe : rounded.toNat ≤ decOut.size + 31 := by
    unfold rounded
    rw [uland_toNat]
    refine le_trans Nat.and_le_right ?_
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hdecSize,
      show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_le _ _
  have hptr_toNat : ptr.toNat = 160 + rounded.toNat := by
    unfold ptr
    rw [uadd_toNat, show (⟨160⟩ : UInt256).toNat = 160 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hroundSmall : rounded.toNat < 64 := by omega
      have hsz : UInt256.size = 2 ^ 256 := by decide
      omega)
  have hltPtr : UInt256.lt ptr (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    rw [hptr_toNat, show (⟨160⟩ : UInt256).toNat = 160 from by decide]
    omega
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtPtr :
      UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hptr_toNat, hmax64]
    omega
  have hallocOk :
      UInt256.lor (UInt256.lt ptr (⟨160⟩ : UInt256))
        (UInt256.gt ptr (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨0⟩ := by
    rw [hltPtr, hgtPtr]
    native_decide
  have rd3071 := evm_run rd1506 with [
    push2 ⟨1548⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨1510⟩, jump (by jump_dest),
    jumpdest, push2 ⟨1520⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperDecimalsPostShortDecodeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd1520 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest]
  have hlenCheck :
      UInt256.slt (UInt256.sub ((⟨160⟩ : UInt256) + rdsz) ⟨160⟩) ⟨32⟩ = ⟨1⟩ := by
    simpa [rdsz] using
      solcReturnStaticLenCheckShort (base := 160) (words := 1) (by simpa using hshort)
        (by norm_num [UInt256.size])
        (by
          have hcap : (2 : ℕ) ^ 255 + 160 < UInt256.size := by norm_num [UInt256.size]
          have hhi : decOut.size < 2 ^ 255 := by omega
          omega)
        (by norm_num)
  have rd1524₀ := evm_run rd1520 with [
    dup2, add, sub, slt]
  have rd1524 := rd1524₀
  rw [hlenCheck] at rd1524
  have rd670 := evm_run rd1524 with [
    push2 ⟨670⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd670 with [jumpdest, pop, dup1, raw rev 0 (by native_decide) mem_cost
    (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : ¬ (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let decWord : UInt256 := setRewardConfigDecimalsReturnWord decOut
  have hdec8' : ¬ decWord.toNat < EVM.twoPow 8 := by
    simpa [decWord] using hdec8
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hdec32
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨1⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd1506₀ := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨1499⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup5, dup2, dup2, returndatasize, dup4, gt]
  have rd1506 := rd1506₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd1506
  have rd3071 := evm_run rd1506 with [
    push2 ⟨1548⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨1520⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd1524 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd1536 := evm_run rd1524 with [
    raw mload 0 decWord setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigWrapperDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hnotClean : UInt256.land decWord uint8Mask ≠ decWord :=
    uint8Mask_not_clean hdec8'
  have hneq : decWord ≠ UInt256.land decWord uint8Mask := by
    intro hEq
    exact hnotClean hEq.symm
  have hsub : UInt256.sub decWord (UInt256.land decWord uint8Mask) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hneq
  have rd667 := evm_run rd1536 with [
    push2 ⟨667⟩, jumpiT (by simpa [uint8Mask] using hsub) (by jump_dest)]
  exact evm_run rd667 with [jumpdest, dup1, raw rev 0 (by native_decide) mem_cost
    (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_pow10_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hgt77 : 77 < (setRewardConfigDecimalsReturnWord decOut).toNat) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let decWord : UInt256 := setRewardConfigDecimalsReturnWord decOut
  have hdec8' : decWord.toNat < EVM.twoPow 8 := by
    simpa [decWord] using hdec8
  have hgt77' : 77 < decWord.toNat := by
    simpa [decWord] using hgt77
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hdec32
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨1⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd1506₀ := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨1499⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup5, dup2, dup2, returndatasize, dup4, gt]
  have rd1506 := rd1506₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd1506
  have rd3071 := evm_run rd1506 with [
    push2 ⟨1548⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨1520⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd1524 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd1536 := evm_run rd1524 with [
    raw mload 0 decWord setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigWrapperDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd1536zero := rd1536
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd1536zero
  have rd1176 := evm_run rd1536zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨1168⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hgt77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨1⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_one
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hgt77'
  have rd1176gt := rd1176
  rw [hgt77Word] at rd1176gt
  have rd1478 := evm_run rd1176gt with [
    push2 ⟨1478⟩, jumpiT (by native_decide) (by jump_dest)]
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd1492₀ := evm_run rd1478 with [
    jumpdest, push1 ⟨17⟩, dup7, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl,
    push1 ⟨0⟩]
  have rd1492 := rd1492₀
  rw [hsel] at rd1492
  have rd1493 := evm_run rd1492 with [
    raw mstore 0
      (setRewardConfigPanicMem0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd1498 := evm_run rd1493 with [
    raw mstore 0
      (setRewardConfigPanicMem ⟨17⟩
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd1498 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 3000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_safe64_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hgt64 : 2 ^ 64 - 1 < (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let decWord : UInt256 := setRewardConfigDecimalsReturnWord decOut
  have hdec8' : decWord.toNat < EVM.twoPow 8 := by
    simpa [decWord] using hdec8
  have hle77' : decWord.toNat ≤ 77 := by
    simpa [decWord] using hle77
  have hgt64' : 2 ^ 64 - 1 < (10 : ℕ) ^ decWord.toNat := by
    simpa [decWord] using hgt64
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hdec32
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨1⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd1506₀ := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨1499⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup5, dup2, dup2, returndatasize, dup4, gt]
  have rd1506 := rd1506₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd1506
  have rd3071 := evm_run rd1506 with [
    push2 ⟨1548⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨1520⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd1524 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd1536 := evm_run rd1524 with [
    raw mload 0 decWord setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigWrapperDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd1536zero := rd1536
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd1536zero
  have rd1176 := evm_run rd1536zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨1168⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hle77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨0⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_zero
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hle77'
  have rd1176le := rd1176
  rw [hle77Word] at rd1176le
  let tokenScale : UInt256 := UInt256.exp (⟨10⟩ : UInt256) decWord
  have htokenScale_toNat : tokenScale.toNat = (10 : ℕ) ^ decWord.toNat := by
    unfold tokenScale
    rw [← u256_ofNat_toNat decWord]
    interval_cases decWord.toNat <;> native_decide
  have rd1194 := evm_run rd1176le with [
    push2 ⟨1478⟩, jumpiNT (by native_decide), push1 ⟨10⟩, exp,
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, swap6, dup7, dup3, gt]
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtToken :
      UInt256.gt tokenScale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨1⟩ := by
    apply ugt_one
    rw [htokenScale_toNat, hmax64]
    exact hgt64'
  have hmaskedDec : UInt256.land (⟨255⟩ : UInt256) decWord = decWord := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    simpa [uint8Mask] using hclean
  have rd1194gt := rd1194
  rw [show UInt256.gt (UInt256.exp (⟨10⟩ : UInt256)
        (UInt256.land (⟨255⟩ : UInt256) decWord))
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨1⟩ by
      rw [hmaskedDec]
      simpa [tokenScale] using hgtToken] at rd1194gt
  have rd1458 := evm_run rd1194gt with [
    push2 ⟨1458⟩, jumpiT (by native_decide) (by jump_dest)]
  have hsel :
      UInt256.shiftLeft (⟨0x4809a3⟩ : UInt256) ⟨226⟩ =
        setRewardConfigInvalidUInt64Selector := by
    rfl
  have rd1463pre := evm_run rd1458 with [
    jumpdest, push1 ⟨36⟩, swap2]
  have rd1463 := rdDup12 rd1463pre (by native_decide) (by simp)
  have rd1464 := evm_run rd1463 with [
    raw mload 0 ⟨192⟩ setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (setRewardConfigWrapperDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rd1465 := evm_run rd1464 with [
    swap2]
  have rd1469 := rd1465.pushConst (⟨0x4809a3⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1472₀ := evm_run rd1469 with [
    push1 ⟨226⟩, shl, dup4]
  have rd1472 := rd1472₀
  rw [hsel] at rd1472
  let awInvalidSelector : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigWrapperDecimalsPostCallAw.toNat
      (⟨192⟩ : UInt256).toNat 32)
  let awInvalidArg : UInt256 :=
    UInt256.ofNat (MachineState.M awInvalidSelector.toNat
      ((⟨192⟩ : UInt256) + ⟨4⟩).toNat 32)
  have rd1473 := evm_run rd1472 with [
    raw mstore (Cₘ awInvalidSelector - Cₘ setRewardConfigWrapperDecimalsPostCallAw)
      (setRewardConfigInvalidUInt64SelectorMem
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      awInvalidSelector (by native_decide) mem_cost
      (by unfold setRewardConfigInvalidUInt64SelectorMem; rfl)
      (by rfl) (by evm_ov)]
  have rd1477 := evm_run rd1473 with [
    dup3, add,
    raw mstore (Cₘ awInvalidArg - Cₘ awInvalidSelector)
      (setRewardConfigInvalidUInt64Mem tokenScale
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      awInvalidArg (by native_decide) mem_cost
      (by
        unfold setRewardConfigInvalidUInt64Mem setRewardConfigInvalidUInt64SelectorMem tokenScale
        rw [hmaskedDec]
        rw [show ((⟨192⟩ : UInt256) + ⟨4⟩).toNat = 196 from by native_decide])
      (by rfl) (by evm_ov)]
  exact evm_run rd1477 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_safe64_prefix
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 2 ^ 64 - 1)
    (hbase64 : baseWord.toNat < EVM.twoPow 64) :
    ∃ tokenScale k' C',
      tokenScale.toNat = (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ∧
      UInt256.land baseWord (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = baseWord ∧
      UInt256.land
          (UInt256.exp (⟨10⟩ : UInt256)
            (UInt256.land (⟨255⟩ : UInt256) (setRewardConfigDecimalsReturnWord decOut)))
          (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) =
        tokenScale ∧
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
          (UInt256.land
            (UInt256.exp (⟨10⟩ : UInt256)
              (UInt256.land (⟨255⟩ : UInt256)
                (setRewardConfigDecimalsReturnWord decOut)))
            (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) =
        tokenScale ∧
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1208⟩
        [UInt256.gt baseWord tokenScale, baseWord, tokenScale, solcAddrMask, ⟨32⟩, ⟨224⟩,
          ((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩,
          setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
          ⟨64⟩, ⟨0⟩]
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
        setRewardConfigWrapperDecimalsPostCallAw decOut acc k' C' := by
  let decWord : UInt256 := setRewardConfigDecimalsReturnWord decOut
  have hdec8' : decWord.toNat < EVM.twoPow 8 := by
    simpa [decWord] using hdec8
  have hle77' : decWord.toNat ≤ 77 := by
    simpa [decWord] using hle77
  have hsafe64' : (10 : ℕ) ^ decWord.toNat ≤ 2 ^ 64 - 1 := by
    simpa [decWord] using hsafe64
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hdec32
  have rd1154 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [⟨1⟩, ⟨160⟩, baseWord, solcAddrMask, ⟨32⟩, ⟨224⟩, ⟨4⟩,
        setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
        ⟨64⟩, ⟨0⟩]
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C := by
    simpa [setRewardConfigWrapperDecimalsPostCallStack,
      setRewardConfigWrapperDecimalsPostCallTail] using rd
  have rd1506₀ := evm_run rd1154 with [
    swap1, dup2, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨1499⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup5, dup2, dup2, returndatasize, dup4, gt]
  have rd1506 := rd1506₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd1506
  have rd3071 := evm_run rd1506 with [
    push2 ⟨1548⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨1520⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigWrapperDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd1524 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd1536 := evm_run rd1524 with [
    raw mload 0 decWord setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigWrapperDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd1536zero := rd1536
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd1536zero
  have rd1176 := evm_run rd1536zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨1168⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hle77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨0⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_zero
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hle77'
  have rd1176le := rd1176
  rw [hle77Word] at rd1176le
  let tokenScale : UInt256 := UInt256.exp (⟨10⟩ : UInt256) decWord
  have htokenScale_toNat : tokenScale.toNat = (10 : ℕ) ^ decWord.toNat := by
    unfold tokenScale
    rw [← u256_ofNat_toNat decWord]
    interval_cases decWord.toNat <;> native_decide
  have rd1194 := evm_run rd1176le with [
    push2 ⟨1478⟩, jumpiNT (by native_decide), push1 ⟨10⟩, exp,
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, swap6, dup7, dup3, gt]
  have hmax64 :
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩).toNat =
        18446744073709551615 := by
    native_decide
  have hgtToken :
      UInt256.gt tokenScale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [htokenScale_toNat, hmax64]
    exact hsafe64'
  have hmaskedDec : UInt256.land (⟨255⟩ : UInt256) decWord = decWord := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    simpa [uint8Mask] using hclean
  have rd1194le := rd1194
  rw [show UInt256.gt (UInt256.exp (⟨10⟩ : UInt256)
        (UInt256.land (⟨255⟩ : UInt256) decWord))
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ by
      rw [hmaskedDec]
      simpa [tokenScale] using hgtToken] at rd1194le
  have rd1208 := evm_run rd1194le with [
    push2 ⟨1458⟩, jumpiNT (by native_decide), pop, dup6, and, swap1,
    dup2, dup7, dup3, and, gt]
  have htokenScale64 : tokenScale.toNat < EVM.twoPow 64 := by
    rw [htokenScale_toNat]
    have hpow : (10 : ℕ) ^ decWord.toNat < 2 ^ 64 := by omega
    simpa [EVM.twoPow] using hpow
  have hbaseClean :
      UInt256.land baseWord (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = baseWord := by
    simpa [uint64Mask] using uint64Mask_clean hbase64
  have htokenClean :
      UInt256.land (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord))
        (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = tokenScale := by
    rw [hmaskedDec]
    simpa [tokenScale, uint64Mask] using uint64Mask_clean htokenScale64
  have htokenCleanDirect :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
        (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord)) =
        tokenScale := by
    rw [u256_land_comm (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
      (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord))]
    exact htokenClean
  have htokenCleanMaskLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) tokenScale =
        tokenScale := by
    rw [u256_land_comm (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) tokenScale]
    simpa [uint64Mask] using uint64Mask_clean htokenScale64
  have htokenCleanLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
        (UInt256.land
          (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord))
          (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = tokenScale := by
    rw [htokenClean]
    exact htokenCleanMaskLeft
  have rd1208clean := rd1208
  rw [hbaseClean, htokenCleanDirect] at rd1208clean
  obtain ⟨k1208, C1208, rd1208final⟩ : ∃ k1208 C1208,
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1208⟩
        [UInt256.gt baseWord tokenScale, baseWord, tokenScale, solcAddrMask, ⟨32⟩, ⟨224⟩,
          ((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩,
          setRewardConfigCometWord I, ⟨1⟩, setRewardConfigWrapperDecimalsTargetWord I,
          ⟨64⟩, ⟨0⟩]
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut)
        setRewardConfigWrapperDecimalsPostCallAw decOut acc k1208 C1208 := by
    exact ⟨_, _, by
      simpa [decWord, tokenScale] using rd1208clean⟩
  refine ⟨tokenScale, k1208, C1208, ?_⟩
  refine ⟨?_, hbaseClean, ?_, ?_, rd1208final⟩
  · simpa [decWord] using htokenScale_toNat
  · simpa [decWord] using htokenClean
  · simpa [decWord] using htokenCleanLeft

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_upscale_zero_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 2 ^ 64 - 1)
    (hbase64 : baseWord.toNat < EVM.twoPow 64)
    (hle : baseWord.toNat ≤
      (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat)
    (hbase0 : baseWord = ⟨0⟩) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨tokenScale, _, _, htokenScale_toNat, hbaseClean, _htokenClean,
      _htokenCleanLeft, rd1208⟩ :=
    cometRewardsSetRewardConfigX_after_decimals_safe64_prefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (baseOut := baseOut) (decOut := decOut)
      (baseWord := baseWord) (acc := acc) (k := k) (C := C)
      rd hdec32 hdecSize hdec8 hle77 hsafe64 hbase64
  have hupWord : UInt256.gt baseWord tokenScale = ⟨0⟩ := by
    apply ugt_zero
    rw [htokenScale_toNat]
    exact hle
  have rd1208up := rd1208
  rw [hupWord] at rd1208up
  have rd1337 := evm_run rd1208up with [
    push1 ⟨0⟩, eq, push2 ⟨1337⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest]
  have rd3137 := evm_run rd1337 with [
    push2 ⟨1346⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest)]
  have rd3156pre := evm_run rd3137 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap2, dup3, and,
    swap2, swap1, dup3, iszero]
  have hdenZero :
      UInt256.isZero
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) baseWord) =
        ⟨1⟩ := by
    rw [hbase0]
    native_decide
  have rd3156 := rd3156pre
  rw [hdenZero] at rd3156
  have rd3161 := evm_run rd3156 with [
    push2 ⟨3161⟩, jumpiT (by native_decide) (by jump_dest)]
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd3172₀ := evm_run rd3161 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push1 ⟨0⟩]
  have rd3172 := rd3172₀
  rw [hsel] at rd3172
  have rd3173 := evm_run rd3172 with [
    raw mstore 0
      (setRewardConfigPanicMem0 (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3178 := evm_run rd3173 with [
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0
      (setRewardConfigPanicMem ⟨18⟩
        (setRewardConfigWrapperDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3178 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_downscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hperm : I.perm = true)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 2 ^ 64 - 1)
    (hbase64 : baseWord.toNat < EVM.twoPow 64)
    (hdown : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat < baseWord.toNat)
    (hrescale : rescale.toNat =
      baseWord.toNat / (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigSlotOf I)
            (setRewardConfigSlot0Down
              (solcSlotWord acc.2 I (setRewardConfigSlotOf I))
              (setRewardConfigTokenWord I) rescale))
          (setRewardConfigSlotOf I + ⟨1⟩)
          setRewardConfigMultiplierWord)
      ByteArray.empty := by
  obtain ⟨tokenScale, _, _, htokenScale_toNat, hbaseClean, _htokenClean,
      _htokenCleanLeft, rd1208⟩ :=
    cometRewardsSetRewardConfigX_after_decimals_safe64_prefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (baseOut := baseOut) (decOut := decOut)
      (baseWord := baseWord) (acc := acc) (k := k) (C := C)
      rd hdec32 hdecSize hdec8 hle77 hsafe64 hbase64
  have hdownWord : UInt256.gt baseWord tokenScale = ⟨1⟩ := by
    apply ugt_one
    rw [htokenScale_toNat]
    exact hdown
  have htokenScale64 : tokenScale.toNat < EVM.twoPow 64 := by
    rw [htokenScale_toNat]
    have hpow :
        (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat < 2 ^ 64 := by
      omega
    simpa [EVM.twoPow] using hpow
  have htokenCleanMaskLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) tokenScale =
        tokenScale := by
    rw [u256_land_comm (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) tokenScale]
    simpa [uint64Mask] using uint64Mask_clean htokenScale64
  have htokenNZ : tokenScale ≠ ⟨0⟩ := by
    intro hzero
    have hto := congrArg UInt256.toNat hzero
    rw [htokenScale_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl] at hto
    have hpos : 0 < (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat := by
      positivity
    omega
  have hrescaleWord : UInt256.div baseWord tokenScale = rescale := by
    apply u256_inj
    rw [udiv_toNat, htokenScale_toNat, hrescale]
  have hrescale64 : rescale.toNat < EVM.twoPow 64 := by
    rw [hrescale]
    have hdiv := Nat.div_le_self baseWord.toNat
      ((10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat)
    have hbase64' : baseWord.toNat < 2 ^ 64 := by
      simpa [EVM.twoPow] using hbase64
    simpa [EVM.twoPow] using lt_of_le_of_lt hdiv hbase64'
  have hrescaleClean :
      UInt256.land rescale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = rescale := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have rd1208down := rd1208
  rw [hdownWord] at rd1208down
  have rd1224 := evm_run rd1208down with [
    push1 ⟨0⟩, eq, push2 ⟨1337⟩, jumpiNT (by native_decide),
    swap1, push2 ⟨1224⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap2, dup3, and,
    swap2, swap1, dup3, iszero]
  rw [show UInt256.isZero
      (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) tokenScale) =
        ⟨0⟩ by
      rw [htokenCleanMaskLeft]
      exact isZero_eq_zero_of_ne htokenNZ] at rd1224
  have rd1224ret := evm_run rd1224 with [
    push2 ⟨3161⟩, jumpiNT (by native_decide), and, div, swap1, jump (by jump_dest),
    jumpdest]
  have rd1224rescale := rd1224ret
  rw [hbaseClean, htokenCleanMaskLeft, hrescaleWord] at rd1224rescale
  have rd1237 := evm_run rd1224rescale with [
    swap4, dup9,
    raw mload 0 ⟨192⟩ setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigWrapperDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap8, push2 ⟨1237⟩, dup10, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (setRewardConfigWrapperSuccessFreeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessFreeMem Reasoning.Theory.writeWord; rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rd1239 := evm_run rd1237 with [
    dup9,
    raw mstore 3 (setRewardConfigWrapperSuccessTokenMem I baseOut decOut)
      (⟨7⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessTokenMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1244pre := evm_run rd1239 with [
    dup3, dup9, add, swap5, and]
  have rd1244 := rd1244pre
  rw [hrescaleClean] at rd1244
  have rd1246 := evm_run rd1244 with [
    dup5,
    raw mstore 3 (setRewardConfigWrapperSuccessRescaleMem I baseOut decOut rescale)
      (⟨8⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessRescaleMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1255 := evm_run rd1246 with [
    dup6, dup9, dup9, add, swap3, push1 ⟨0⟩, dup5,
    raw mstore 3 (setRewardConfigWrapperSuccessBitMem I baseOut decOut rescale ⟨0⟩)
      (⟨9⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessBitMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1260 := evm_run rd1255 with [
    push1 ⟨96⟩, dup10, add, swap7]
  have rd1270 := rd1260.pushConst setRewardConfigMultiplierWord
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1271 := evm_run rd1270 with [
    dup9,
    raw mstore 3
      (setRewardConfigWrapperSuccessMultiplierMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessMultiplierMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1274 := evm_run rd1271 with [
    push1 ⟨0⟩,
    raw mstore 0 (setRewardConfigWrapperSuccessCometMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessCometMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1275 := evm_run rd1274 with [
    raw mstore 0 (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessArgsMem; rfl)
      (by native_decide) (by evm_ov)]
  have hslot := setRewardConfigSlotOf_eq_solc I hcanon0
  have hkeccak :=
    setRewardConfigWrapperSuccessArgsMem_keccakSlot I baseOut decOut rescale ⟨0⟩
      hdec32 hdecSize
  have rd1279pre := evm_run rd1275 with [dup8, push1 ⟨0⟩]
  have rd1279₀ := rd1279pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I))
    (⟨10⟩ : UInt256) (by native_decide) mem_cost hkeccak (by native_decide) (by evm_ov)
  have rd1279 := rd1279₀
  rw [← hslot] at rd1279
  have rd1285pre := evm_run rd1279 with [
    swap7,
    raw mload 0 (setRewardConfigWrapperDecimalsTargetWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload192 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup7]
  obtain ⟨_, _, rd1285⟩ := rd1285pre.sload (by native_decide) (by evm_ov)
  have rd1317 := evm_run rd1285 with [
    swap4, push1 ⟨1⟩, push1 ⟨160⟩, shl, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    swap1,
    raw mload 0 rescale (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload224 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    push1 ⟨160⟩, shl, and, swap3, push1 ⟨255⟩, push1 ⟨224⟩, shl, swap2,
    raw mload 0 (⟨0⟩ : UInt256) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload256 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    iszero, iszero, swap1, shl, and, swap3]
  have rd1322 := rd1317.pushConst (⟨0xffffff⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1329 := evm_run rd1322 with [
    push1 ⟨232⟩, shl, and, lor, lor, lor, dup4]
  let oldSlot : UInt256 := solcSlotWord acc.2 I (setRewardConfigSlotOf I)
  have rd1329packed := rd1329
  rw [show
      UInt256.lor
        (UInt256.lor
          (UInt256.lor
            (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) oldSlot)
            (UInt256.land (setRewardConfigWrapperDecimalsTargetWord I) solcAddrMask))
          (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
        (UInt256.land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)
          (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)) =
        setRewardConfigSlot0Down oldSlot (setRewardConfigWrapperDecimalsTargetWord I) rescale by
        exact setRewardConfigWrapperSlot0Down_bytecodeExpr_runtime oldSlot
          (setRewardConfigWrapperDecimalsTargetWord I) rescale] at rd1329packed
  obtain ⟨_, _, rd1329fold⟩ : ∃ k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1330⟩
        [setRewardConfigSlotOf I,
          setRewardConfigSlot0Down oldSlot (setRewardConfigWrapperDecimalsTargetWord I)
            rescale,
          ⟨192⟩ + ⟨96⟩, ⟨1⟩, setRewardConfigSlotOf I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale ⟨0⟩)
        (⟨10⟩ : UInt256) decOut (acc.1, acc.2) k' C' := by
    exact ⟨_, _, by simpa [oldSlot, solcSlotWord] using rd1329packed⟩
  have htargetWord :
      setRewardConfigWrapperDecimalsTargetWord I = setRewardConfigTokenWord I := by
    unfold setRewardConfigWrapperDecimalsTargetWord
    rw [u256_land_comm solcAddrMask (setRewardConfigTokenWord I)]
    exact solcAddrMask_clean hcanon1
  rw [htargetWord] at rd1329fold
  obtain ⟨_, _, rd1330⟩ := rd1329fold.sstore hperm (by native_decide) (by evm_ov)
  have rd1333pre := evm_run rd1330 with [
    raw mload 0 setRewardConfigMultiplierWord (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload288 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap2, add]
  obtain ⟨_, _, rd1334⟩ := rd1333pre.sstore hperm (by native_decide) (by evm_ov)
  have rd1335 := evm_run rd1334 with [
    raw mload 0 ⟨320⟩ (⟨10⟩ : UInt256) (by native_decide)
      mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload64 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rdret : RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigSlotOf I)
            (setRewardConfigSlot0Down oldSlot (setRewardConfigTokenWord I) rescale))
          (setRewardConfigSlotOf I + ⟨1⟩)
          setRewardConfigMultiplierWord)
      ByteArray.empty := by
    exact RD.ret 0 ByteArray.empty rd1335 (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide,
          show (⟨0⟩ : UInt256).toNat = 0 from by decide]
        exact byteArray_readWithPadding_zero _ 320)
      (by simp)
  simpa [oldSlot] using rdret

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigX_after_decimals_upscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1154⟩
      (setRewardConfigWrapperDecimalsPostCallStack true baseWord I)
      (setRewardConfigWrapperDecimalsPostCallMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 2 ^ 64 - 1)
    (hbase64 : baseWord.toNat < EVM.twoPow 64)
    (hperm : I.perm = true)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hle : baseWord.toNat ≤
      (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat)
    (hbaseNZ : baseWord.toNat ≠ 0)
    (hrescale : rescale.toNat =
      (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat / baseWord.toNat) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigSlotOf I)
            (setRewardConfigSlot0Up
              (solcSlotWord acc.2 I (setRewardConfigSlotOf I))
              (setRewardConfigTokenWord I) rescale))
          (setRewardConfigSlotOf I + ⟨1⟩)
          setRewardConfigMultiplierWord)
      ByteArray.empty := by
  obtain ⟨tokenScale, _, _, htokenScale_toNat, hbaseClean, _htokenClean,
      _htokenCleanLeft, rd1208⟩ :=
    cometRewardsSetRewardConfigX_after_decimals_safe64_prefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (baseOut := baseOut) (decOut := decOut)
      (baseWord := baseWord) (acc := acc) (k := k) (C := C)
      rd hdec32 hdecSize hdec8 hle77 hsafe64 hbase64
  have hupWord : UInt256.gt baseWord tokenScale = ⟨0⟩ := by
    apply ugt_zero
    rw [htokenScale_toNat]
    exact hle
  have rd1208up := rd1208
  rw [hupWord] at rd1208up
  have rd1337 := evm_run rd1208up with [
    push1 ⟨0⟩, eq, push2 ⟨1337⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest]
  have rd3137 := evm_run rd1337 with [
    push2 ⟨1346⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest)]
  have rd3156pre := evm_run rd3137 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap2, dup3, and,
    swap2, swap1, dup3, iszero]
  have hbaseNZWord :
      UInt256.isZero
        (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) baseWord) =
        ⟨0⟩ := by
    rw [u256_land_comm (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) baseWord]
    rw [hbaseClean]
    exact isZero_eq_zero_of_ne (by
      intro hzero
      exact hbaseNZ (by
        rw [hzero]
        rfl))
  have rd3156 := rd3156pre
  rw [hbaseNZWord] at rd3156
  have rd1346 := evm_run rd3156 with [
    push2 ⟨3161⟩, jumpiNT (by native_decide), and, div, swap1, jump (by jump_dest),
    jumpdest]
  have htokenScale64 : tokenScale.toNat < EVM.twoPow 64 := by
    rw [htokenScale_toNat]
    have hpow :
        (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat < 2 ^ 64 := by
      omega
    simpa [EVM.twoPow] using hpow
  have htokenCleanRight :
      UInt256.land tokenScale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) =
        tokenScale := by
    simpa [uint64Mask] using uint64Mask_clean htokenScale64
  have hbaseCleanLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) baseWord =
        baseWord := by
    rw [u256_land_comm (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) baseWord]
    exact hbaseClean
  have hrescaleWord : UInt256.div tokenScale baseWord = rescale := by
    apply u256_inj
    rw [udiv_toNat, htokenScale_toNat, hrescale]
  have rd1346rescale := rd1346
  rw [htokenCleanRight, hbaseCleanLeft, hrescaleWord] at rd1346rescale
  have hrescale64 : rescale.toNat < EVM.twoPow 64 := by
    rw [hrescale]
    have hdiv :=
      Nat.div_le_self ((10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat)
        baseWord.toNat
    have hpow :
        (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat < 2 ^ 64 := by
      omega
    exact lt_of_le_of_lt hdiv (by simpa [EVM.twoPow] using hpow)
  have hrescaleClean :
      UInt256.land rescale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = rescale := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have rd1359 := evm_run rd1346rescale with [
    swap4, dup9,
    raw mload 0 ⟨192⟩ setRewardConfigWrapperDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigWrapperDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap8, push2 ⟨1359⟩, dup10, push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (setRewardConfigWrapperSuccessFreeMem I baseOut decOut)
      setRewardConfigWrapperDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessFreeMem Reasoning.Theory.writeWord; rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rd1361 := evm_run rd1359 with [
    dup9,
    raw mstore 3 (setRewardConfigWrapperSuccessTokenMem I baseOut decOut)
      (⟨7⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessTokenMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1366pre := evm_run rd1361 with [
    dup3, dup9, add, swap5, and]
  have rd1366 := rd1366pre
  rw [hrescaleClean] at rd1366
  have rd1368 := evm_run rd1366 with [
    dup5,
    raw mstore 3 (setRewardConfigWrapperSuccessRescaleMem I baseOut decOut rescale)
      (⟨8⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessRescaleMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1376 := evm_run rd1368 with [
    dup6, dup9, dup9, add, swap3, dup2, dup5,
    raw mstore 3 (setRewardConfigWrapperSuccessBitMem I baseOut decOut rescale ⟨1⟩)
      (⟨9⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessBitMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1381 := evm_run rd1376 with [
    push1 ⟨96⟩, dup10, add, swap7]
  have rd1391 := rd1381.pushConst setRewardConfigMultiplierWord
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1392 := evm_run rd1391 with [
    dup9,
    raw mstore 3
      (setRewardConfigWrapperSuccessMultiplierMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessMultiplierMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1395 := evm_run rd1392 with [
    push1 ⟨0⟩,
    raw mstore 0 (setRewardConfigWrapperSuccessCometMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessCometMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd1396 := evm_run rd1395 with [
    raw mstore 0 (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigWrapperSuccessArgsMem; rfl)
      (by native_decide) (by evm_ov)]
  have hslot := setRewardConfigSlotOf_eq_solc I hcanon0
  have hkeccak :=
    setRewardConfigWrapperSuccessArgsMem_keccakSlot I baseOut decOut rescale ⟨1⟩
      hdec32 hdecSize
  have rd1400pre := evm_run rd1396 with [dup8, push1 ⟨0⟩]
  have rd1400₀ := rd1400pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigCometWord I))
    (⟨10⟩ : UInt256) (by native_decide) mem_cost hkeccak (by native_decide) (by evm_ov)
  have rd1400 := rd1400₀
  rw [← hslot] at rd1400
  have rd1406pre := evm_run rd1400 with [
    swap7,
    raw mload 0 (setRewardConfigWrapperDecimalsTargetWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload192 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup7]
  obtain ⟨_, _, rd1406⟩ := rd1406pre.sload (by native_decide) (by evm_ov)
  have rd1438 := evm_run rd1406 with [
    swap4, push1 ⟨1⟩, push1 ⟨160⟩, shl, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    swap1,
    raw mload 0 rescale (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload224 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    push1 ⟨160⟩, shl, and, swap3, push1 ⟨255⟩, push1 ⟨224⟩, shl, swap2,
    raw mload 0 (⟨1⟩ : UInt256) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload256 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    iszero, iszero, swap1, shl, and, swap3]
  have rd1443 := rd1438.pushConst (⟨0xffffff⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1450 := evm_run rd1443 with [
    push1 ⟨232⟩, shl, and, lor, lor, lor, dup4]
  let oldSlot : UInt256 := solcSlotWord acc.2 I (setRewardConfigSlotOf I)
  have rd1450packed := rd1450
  rw [show
      UInt256.lor
        (UInt256.lor
          (UInt256.lor
            (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) oldSlot)
            (UInt256.land (setRewardConfigWrapperDecimalsTargetWord I) solcAddrMask))
          (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
        (UInt256.land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)
          (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)) =
        setRewardConfigSlot0Up oldSlot (setRewardConfigWrapperDecimalsTargetWord I) rescale by
        exact setRewardConfigWrapperSlot0Up_bytecodeExpr_runtime oldSlot
          (setRewardConfigWrapperDecimalsTargetWord I) rescale] at rd1450packed
  obtain ⟨_, _, rd1450fold⟩ : ∃ k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1451⟩
        [setRewardConfigSlotOf I,
          setRewardConfigSlot0Up oldSlot (setRewardConfigWrapperDecimalsTargetWord I)
            rescale,
          ⟨192⟩ + ⟨96⟩, ⟨1⟩, setRewardConfigSlotOf I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigWrapperSuccessArgsMem I baseOut decOut rescale ⟨1⟩)
        (⟨10⟩ : UInt256) decOut (acc.1, acc.2) k' C' := by
    exact ⟨_, _, by simpa [oldSlot, solcSlotWord] using rd1450packed⟩
  have htargetWord :
      setRewardConfigWrapperDecimalsTargetWord I = setRewardConfigTokenWord I := by
    unfold setRewardConfigWrapperDecimalsTargetWord
    rw [u256_land_comm solcAddrMask (setRewardConfigTokenWord I)]
    exact solcAddrMask_clean hcanon1
  rw [htargetWord] at rd1450fold
  obtain ⟨_, _, rd1451⟩ := rd1450fold.sstore hperm (by native_decide) (by evm_ov)
  have rd1454pre := evm_run rd1451 with [
    raw mload 0 setRewardConfigMultiplierWord (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload288 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap2, add]
  obtain ⟨_, _, rd1455⟩ := rd1454pre.sstore hperm (by native_decide) (by evm_ov)
  have rd1456 := evm_run rd1455 with [
    raw mload 0 ⟨320⟩ (⟨10⟩ : UInt256) (by native_decide)
      mem_cost
      (setRewardConfigWrapperSuccessArgsMem_mload64 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rdret : RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigSlotOf I)
            (setRewardConfigSlot0Up oldSlot (setRewardConfigTokenWord I) rescale))
          (setRewardConfigSlotOf I + ⟨1⟩)
          setRewardConfigMultiplierWord)
      ByteArray.empty := by
    exact RD.ret 0 ByteArray.empty rd1456 (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [show (⟨320⟩ : UInt256).toNat = 320 from by decide,
          show (⟨0⟩ : UInt256).toNat = 0 from by decide]
        exact byteArray_readWithPadding_zero _ 320)
      (by simp)
  simpa [oldSlot] using rdret

theorem cometRewardsSetRewardConfigBodyCore_auth_revert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I (cometRewardsSelBytes 7))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ_evm I ≠ solcSourceWord I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hd := cometRewardsDispatch_setRewardConfig (cd := I.calldata) hsel
  have hdec := cometRewardsDecode_setRewardConfig_ok (I := I) hsz68 hhi hcanon0 hcanon1
  have hgovWord : governorWord σ_evm I = governorWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
  have hgovRet : governorReturnWord σ_evm I = governorReturnWord σ_solm I := by
    simp [governorReturnWord, hgovWord]
  have hauthSolm : governorReturnWord σ_solm I ≠ solcSourceWord I := by
    intro h
    exact hauth (by rw [hgovRet, h])
  have hgovSolm :
      UInt256.land (Solm.EVM.storageLoad
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
        ⟨0⟩) solcAddrMask ≠
        solcSourceWord
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv := by
    simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using hauthSolm
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (setRewardConfigStore I) setRewardConfigTransition.body .reverted := by
    exact cometRewardsSetRewardConfigBodyReverts_auth
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
      (by simp only [initState]; exact hwv)
      (by simp only [initState]; exact hhi)
      hgovSolm
  exact (cometRewardsSetRewardConfigX_revert_auth
      (g := Sat256.ofUInt256 g) hwv hsz68 hsize hhi hcanon0 hcanon1 hauth hreach)
    |>.reEquivExecutionRevert hcode hd hdec hbody

/-- `setRewardConfig(address,address)` body, reached at pc 1009. -/
theorem cometRewardsSetRewardConfigBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 7))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) setRewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsSetRewardConfigSelector_size hsel
  have hd := cometRewardsDispatch_setRewardConfig (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonComet : (setRewardConfigCometWord I).toNat < EVM.addressModulus
      · by_cases hcanonToken : (setRewardConfigTokenWord I).toNat < EVM.addressModulus
        · have hdec :=
            cometRewardsDecode_setRewardConfig_ok (I := I) hsz68 hhi hcanonComet hcanonToken
          by_cases hauth : governorReturnWord σ_evm I ≠ solcSourceWord I
          · exact cometRewardsSetRewardConfigBodyCore_auth_revert
              hcode hsize hwv hsel hreach hAccounts hsz68 hhi hcanonComet hcanonToken hauth
          · have hauthEq : governorReturnWord σ_evm I = solcSourceWord I :=
              Classical.not_not.mp hauth
            have hgovWord : governorWord σ_evm I = governorWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
            have hgovRet :
                governorReturnWord σ_evm I = governorReturnWord σ_solm I := by
              simp [governorReturnWord, hgovWord]
            have hauthSolm : governorReturnWord σ_solm I = solcSourceWord I := by
              rw [← hgovRet]
              exact hauthEq
            have hgovSolm :
                UInt256.land (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨0⟩) solcAddrMask =
                  solcSourceWord
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv := by
              simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using hauthSolm
            have hslotWord :
                solcSlotWord σ_evm I (setRewardConfigSlotOf I) =
                  solcSlotWord σ_solm I (setRewardConfigSlotOf I) :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner
                (setRewardConfigSlotOf I) ⟨0⟩
            by_cases hconfigured :
                UInt256.land (solcSlotWord σ_evm I (setRewardConfigSlotOf I))
                  solcAddrMask ≠ ⟨0⟩
            · have hconfiguredSolm :
                  UInt256.land (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (setRewardConfigSlotOf I)) solcAddrMask ≠ ⟨0⟩ := by
                simpa [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                  hslotWord] using hconfigured
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (setRewardConfigStore I) setRewardConfigTransition.body .reverted := by
                exact cometRewardsSetRewardConfigBodyReverts_configured
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                  (by simp only [initState]; exact hwv)
                  (by simp only [initState]; exact hhi)
                  hgovSolm
                  hconfiguredSolm
              exact (cometRewardsSetRewardConfigX_revert_configured
                  (g := Sat256.ofUInt256 g)
                  hwv hsz68 hsize hhi hcanonComet hcanonToken hauthEq hconfigured hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · have htokenZero :
                  UInt256.land (solcSlotWord σ_evm I (setRewardConfigSlotOf I))
                    solcAddrMask = ⟨0⟩ := by
                exact Classical.not_not.mp hconfigured
              have htokenZeroSolm :
                  UInt256.land (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (setRewardConfigSlotOf I)) solcAddrMask = ⟨0⟩ := by
                simpa [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                  hslotWord] using htokenZero
              by_cases hdepth : I.depth.val < 1024
              · obtain ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, kPost, CPost,
                    hcallS, hPostAccounts, rdPost, houtSign⟩ :=
                  cometRewardsSetRewardConfigX_call_baseAccrualScale_made
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hsz68 hsize hhi hcanonComet hcanonToken hauthEq htokenZero hdepth
                    hreach hAccounts
                let evmPost : EVM.State :=
                  { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ'_solm
                      substate := A'_solm
                      createdAccounts := cA' }
                have houtSize : out.size < UInt256.size := lt_size_of_lt_sign houtSign
                cases z
                · have hbody :
                      ExecTransitionBody config contract
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (setRewardConfigStore I)
                        setRewardConfigTransition.body .reverted := by
                    exact cometRewardsSetRewardConfigBodyReverts_baseCallFailure
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      evmPost I
                      (by simp only [initState]; exact hwv)
                      (by simp only [initState]; exact hhi)
                      hgovSolm
                      htokenZeroSolm
                      (by simpa [evmPost] using hcallS)
                  exact
                    (cometRewardsSetRewardConfigX_after_baseAccrualScale_failure
                        rdPost houtSize)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases hshort : out.size < 32
                  · have hdecBase := cometRewardsBaseAccrualScale_decode_none_short
                      (out := out) hshort
                    have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (setRewardConfigStore I)
                          setRewardConfigTransition.body .reverted := by
                      exact cometRewardsSetRewardConfigBodyReverts_baseDecodeFailure
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        evmPost I
                        (by simp only [initState]; exact hwv)
                        (by simp only [initState]; exact hhi)
                        hgovSolm
                        htokenZeroSolm
                        (by simpa [evmPost] using hcallS)
                        hdecBase
                    exact
                      (cometRewardsSetRewardConfigX_after_baseAccrualScale_short_revert
                          rdPost hshort houtSize)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                  · have hout32 : 32 ≤ out.size := by omega
                    by_cases hbaseWord :
                        fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64
                    · have hdecBase := cometRewardsBaseAccrualScale_decode_ok
                        (out := out) hout32 houtSign hbaseWord
                      obtain ⟨kBase, CBase, rdBase⟩ :=
                        cometRewardsSetRewardConfigX_after_baseAccrualScale_decode_ok
                          rdPost hout32 houtSize (by
                            have hto :
                                (setRewardConfigBaseReturnWord out).toNat =
                                  fromByteArrayBigEndian (out.extract 0 32) := by
                              simpa [setRewardConfigBaseReturnWord] using
                                UInt256.toNat_ofNat_of_lt
                                  (fromByteArrayBigEndian_extract0_32_lt hout32)
                            rw [hto]
                            exact hbaseWord)
                      obtain ⟨cA'', σ''_evm, σ''_solm, A''_solm, zDec, outDec,
                          kDec, CDec, hcallDec, hPostAccountsDec, rdDecPost,
                          houtDecSign⟩ :=
                        cometRewardsSetRewardConfigX_call_decimals_made
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g) (baseOut := out)
                          (baseWord := setRewardConfigBaseReturnWord out)
                          (cA' := cA') (σ'_evm := σ'_evm) (σ'_solm := σ'_solm)
                          (A'_solm := A'_solm)
                          hcanonToken hdepth hPostAccounts rdBase hout32 houtSize
                      cases zDec
                      · let evmDecFail : EVM.State :=
                          { evmPost with
                              accountMap := σ''_solm
                              substate := A''_solm
                              createdAccounts := cA'' }
                        have houtDecSize : outDec.size < UInt256.size :=
                          lt_size_of_lt_sign houtDecSign
                        have hbody :
                            ExecTransitionBody config contract
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              (setRewardConfigStore I)
                              setRewardConfigTransition.body .reverted := by
                          exact
                            cometRewardsSetRewardConfigBodyReverts_decimalsCallFailure
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              evmPost evmDecFail I
                              (by simp only [initState]; exact hwv)
                              (by simp only [initState]; exact hhi)
                              hgovSolm
                              htokenZeroSolm
                              (by simpa [evmPost] using hcallS)
                              hdecBase
                              (by simpa [evmPost, evmDecFail] using hcallDec)
                        exact
                          (cometRewardsSetRewardConfigX_after_decimals_failure
                              rdDecPost hout32 houtSize houtDecSize)
                            |>.reEquivExecutionRevert hcode hd hdec hbody
                      · by_cases hdecShort : outDec.size < 32
                        · let evmDecPost : EVM.State :=
                            { evmPost with
                                accountMap := σ''_solm
                                substate := A''_solm
                                createdAccounts := cA'' }
                          have houtDecSize : outDec.size < UInt256.size :=
                            lt_size_of_lt_sign houtDecSign
                          have hdecDecimals := cometRewardsDecimals_decode_none_short
                            (out := outDec) hdecShort
                          have hbody :
                              ExecTransitionBody config contract
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                (setRewardConfigStore I)
                                setRewardConfigTransition.body .reverted := by
                            exact
                              cometRewardsSetRewardConfigBodyReverts_decimalsDecodeFailure
                                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                evmPost evmDecPost I
                                (by simp only [initState]; exact hwv)
                                (by simp only [initState]; exact hhi)
                                hgovSolm
                                htokenZeroSolm
                                (by simpa [evmPost] using hcallS)
                                hdecBase
                                (by simpa [evmPost, evmDecPost] using hcallDec)
                                hdecDecimals
                          exact
                            (cometRewardsSetRewardConfigX_after_decimals_short_revert
                                rdDecPost hdecShort houtDecSize)
                              |>.reEquivExecutionRevert hcode hd hdec hbody
                        · have houtDec32 : 32 ≤ outDec.size := le_of_not_gt hdecShort
                          by_cases hdecWord :
                              fromByteArrayBigEndian (outDec.extract 0 32) < EVM.twoPow 8
                          · have hdecDecimals := cometRewardsDecimals_decode_ok
                              (out := outDec) houtDec32 houtDecSign hdecWord
                            have htoDec :
                                (setRewardConfigDecimalsReturnWord outDec).toNat =
                                  fromByteArrayBigEndian (outDec.extract 0 32) := by
                              simpa [setRewardConfigDecimalsReturnWord] using
                                UInt256.toNat_ofNat_of_lt
                                  (fromByteArrayBigEndian_extract0_32_lt houtDec32)
                            by_cases hle77 :
                                fromByteArrayBigEndian (outDec.extract 0 32) ≤ 77
                            · let evmDecPost : EVM.State :=
                                { evmPost with
                                    accountMap := σ''_solm
                                    substate := A''_solm
                                    createdAccounts := cA'' }
                              have houtDecSize : outDec.size < UInt256.size :=
                                lt_size_of_lt_sign houtDecSign
                              by_cases hsafe64 :
                                  (10 : ℕ) ^
                                    fromByteArrayBigEndian (outDec.extract 0 32) ≤
                                      2 ^ 64 - 1
                              · have hdec8Return :
                                    (setRewardConfigDecimalsReturnWord outDec).toNat <
                                      EVM.twoPow 8 := by
                                  rw [htoDec]
                                  exact hdecWord
                                have hle77Return :
                                    (setRewardConfigDecimalsReturnWord outDec).toNat ≤ 77 := by
                                  rw [htoDec]
                                  exact hle77
                                have hsafe64Return :
                                    (10 : ℕ) ^
                                        (setRewardConfigDecimalsReturnWord outDec).toNat ≤
                                      2 ^ 64 - 1 := by
                                  rw [htoDec]
                                  exact hsafe64
                                have hbaseTo :
                                    (setRewardConfigBaseReturnWord out).toNat =
                                      fromByteArrayBigEndian (out.extract 0 32) := by
                                  simpa [setRewardConfigBaseReturnWord] using
                                    UInt256.toNat_ofNat_of_lt
                                      (fromByteArrayBigEndian_extract0_32_lt hout32)
                                have hbase64Return :
                                    (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64 := by
                                  rw [hbaseTo]
                                  exact hbaseWord
                                have hdecBaseReturn :
                                    config.externalABI.decode? "baseAccrualScale" out =
                                      some [.int (Int.ofNat
                                        (setRewardConfigBaseReturnWord out).toNat)] := by
                                  rw [hbaseTo]
                                  exact hdecBase
                                have hdecDecimalsReturn :
                                    config.externalABI.decode? "decimals" outDec =
                                      some [.int (Int.ofNat
                                        (setRewardConfigDecimalsReturnWord outDec).toNat)] := by
                                  rw [htoDec]
                                  exact hdecDecimals
                                by_cases hdown :
                                    (10 : ℕ) ^
                                        (setRewardConfigDecimalsReturnWord outDec).toNat <
                                      (setRewardConfigBaseReturnWord out).toNat
                                · let rescale : UInt256 := UInt256.ofNat
                                      ((setRewardConfigBaseReturnWord out).toNat /
                                        (10 : ℕ) ^
                                          (setRewardConfigDecimalsReturnWord outDec).toNat)
                                  have hquotLt :
                                      (setRewardConfigBaseReturnWord out).toNat /
                                          (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat <
                                        UInt256.size := by
                                    exact lt_of_le_of_lt
                                      (Nat.div_le_self _ _)
                                      (lt_of_lt_of_le hbase64Return
                                        (by norm_num [EVM.twoPow, UInt256.size]))
                                  have hrescale :
                                      rescale.toNat =
                                        (setRewardConfigBaseReturnWord out).toNat /
                                          (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat := by
                                    simpa [rescale] using UInt256.toNat_ofNat_of_lt hquotLt
                                  have hbody :
                                      ExecTransitionBody config contract
                                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                        (setRewardConfigStore I)
                                        setRewardConfigTransition.body
                                        (.returned
                                          (resumeAfterInternalCall
                                            (setRewardConfigFrame
                                              (initState cA gh bl σ_solm σ₀
                                                (Sat256.ofUInt256 g) A I) I) "_set" none)
                                          (setRewardConfigWrapperSourceFinal evmDecPost I rescale false)
                                          none) := by
                                    exact
                                      cometRewardsSetRewardConfigBodyReturns_downscale
                                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                        evmPost evmDecPost I
                                        hcanonToken
                                        (by simp only [initState]; exact hwv)
                                        (by simp only [initState]; exact hhi)
                                        hgovSolm htokenZeroSolm
                                        (by simpa [evmPost] using hcallS)
                                        hdecBaseReturn
                                        (by simpa [evmPost, evmDecPost] using hcallDec)
                                        hdecDecimalsReturn hle77Return hsafe64Return
                                        hrescale hdown
                                  have hslotPost :
                                      solcSlotWord σ''_evm I (setRewardConfigSlotOf I) =
                                        solcSlotWord σ''_solm I (setRewardConfigSlotOf I) :=
                                    accountMapEquiv_storage_findD hPostAccountsDec I.codeOwner
                                      (setRewardConfigSlotOf I) ⟨0⟩
                                  have hIdeal :=
                                    accountMapEquiv_sstoreAccountMap I.codeOwner
                                      (setRewardConfigSlotOf I + ⟨1⟩)
                                      setRewardConfigMultiplierWord
                                      (accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (setRewardConfigSlotOf I)
                                        (setRewardConfigSlot0Down
                                          (solcSlotWord σ''_solm I (setRewardConfigSlotOf I))
                                          (setRewardConfigTokenWord I) rescale)
                                        hPostAccountsDec)
                                  have hsourceAccounts :=
                                    setRewardConfigWrapperSourceFinal_accountMap_equiv
                                      evmDecPost I rescale false
                                  have hAccountsPost := accountMapEquiv.trans
                                    (by simpa [hslotPost] using hIdeal)
                                    (by
                                      simpa [evmDecPost, evmPost, initState, solcSlotWord,
                                        Solm.EVM.storageLoad, State.lookupAccount,
                                        setRewardConfigSlot0Down] using hsourceAccounts)
                                  have hcreated :
                                      cA'' =
                                        (setRewardConfigWrapperSourceFinal evmDecPost I rescale false).createdAccounts := by
                                    simp [setRewardConfigWrapperSourceFinal,
                                      setRewardConfigWrapperSourceAfterShouldUpscale,
                                      setRewardConfigWrapperSourceAfterRescale,
                                      setRewardConfigWrapperSourceAfterToken, evmDecPost,
                                      storageStore_createdAccounts]
                                  exact
                                    (cometRewardsSetRewardConfigX_after_decimals_downscale_success
                                        rdDecPost hperm hcanonComet hcanonToken houtDec32
                                        houtDecSize hdec8Return hle77Return hsafe64Return
                                        hbase64Return hdown hrescale)
                                      |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                                        hcreated
                                        (by simpa [evmDecPost, hslotPost.symm] using hAccountsPost)
                                        (returnEquiv.fallthrough rfl (by rfl) (by native_decide))
                                · have hupLe :
                                      (setRewardConfigBaseReturnWord out).toNat ≤
                                        (10 : ℕ) ^
                                          (setRewardConfigDecimalsReturnWord outDec).toNat :=
                                    Nat.le_of_not_gt hdown
                                  by_cases hbaseZero :
                                      (setRewardConfigBaseReturnWord out).toNat = 0
                                  · have hbody :
                                      ExecTransitionBody config contract
                                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                        (setRewardConfigStore I)
                                        setRewardConfigTransition.body .reverted := by
                                      exact
                                        cometRewardsSetRewardConfigBodyReverts_upscaleZero
                                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                          evmPost evmDecPost I hcanonToken
                                          (by simp only [initState]; exact hwv)
                                          (by simp only [initState]; exact hhi)
                                          hgovSolm htokenZeroSolm
                                          (by simpa [evmPost] using hcallS)
                                          hdecBaseReturn
                                          (by simpa [evmPost, evmDecPost] using hcallDec)
                                          hdecDecimalsReturn hle77Return hsafe64Return hbaseZero
                                    have hbaseWordZero : setRewardConfigBaseReturnWord out = ⟨0⟩ := by
                                      apply u256_inj
                                      simpa using hbaseZero
                                    exact
                                      (cometRewardsSetRewardConfigX_after_decimals_upscale_zero_revert
                                          rdDecPost houtDec32 houtDecSize hdec8Return
                                          hle77Return hsafe64Return hbase64Return hupLe
                                          hbaseWordZero)
                                        |>.reEquivExecutionRevert hcode hd hdec hbody
                                  · let rescale : UInt256 := UInt256.ofNat
                                      ((10 : ℕ) ^
                                          (setRewardConfigDecimalsReturnWord outDec).toNat /
                                        (setRewardConfigBaseReturnWord out).toNat)
                                    have hquotLt :
                                        (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat /
                                          (setRewardConfigBaseReturnWord out).toNat <
                                          UInt256.size := by
                                      have hdiv :=
                                        Nat.div_le_self
                                          ((10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat)
                                          (setRewardConfigBaseReturnWord out).toNat
                                      have hpowLt :
                                          (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat <
                                          2 ^ 64 := by
                                        omega
                                      exact lt_of_le_of_lt hdiv (by
                                        norm_num [UInt256.size] at hpowLt ⊢
                                        omega)
                                    have hrescale :
                                        rescale.toNat =
                                          (10 : ℕ) ^
                                              (setRewardConfigDecimalsReturnWord outDec).toNat /
                                            (setRewardConfigBaseReturnWord out).toNat := by
                                      simpa [rescale] using UInt256.toNat_ofNat_of_lt hquotLt
                                    have hbody :
                                        ExecTransitionBody config contract
                                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                          (setRewardConfigStore I)
                                          setRewardConfigTransition.body
                                          (.returned
                                            (resumeAfterInternalCall
                                              (setRewardConfigFrame
                                                (initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I) I) "_set" none)
                                            (setRewardConfigWrapperSourceFinal evmDecPost I rescale true)
                                            none) := by
                                      exact
                                        cometRewardsSetRewardConfigBodyReturns_upscale
                                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                          evmPost evmDecPost I hcanonToken
                                          (by simp only [initState]; exact hwv)
                                          (by simp only [initState]; exact hhi)
                                          hgovSolm htokenZeroSolm
                                          (by simpa [evmPost] using hcallS)
                                          hdecBaseReturn
                                          (by simpa [evmPost, evmDecPost] using hcallDec)
                                          hdecDecimalsReturn hle77Return hsafe64Return
                                          hrescale hupLe hbaseZero
                                    have hslotPost :
                                        solcSlotWord σ''_evm I (setRewardConfigSlotOf I) =
                                          solcSlotWord σ''_solm I (setRewardConfigSlotOf I) :=
                                      accountMapEquiv_storage_findD hPostAccountsDec I.codeOwner
                                        (setRewardConfigSlotOf I) ⟨0⟩
                                    have hIdeal :=
                                      accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (setRewardConfigSlotOf I + ⟨1⟩)
                                        setRewardConfigMultiplierWord
                                        (accountMapEquiv_sstoreAccountMap I.codeOwner
                                          (setRewardConfigSlotOf I)
                                          (setRewardConfigSlot0Up
                                            (solcSlotWord σ''_solm I (setRewardConfigSlotOf I))
                                            (setRewardConfigTokenWord I) rescale)
                                          hPostAccountsDec)
                                    have hsourceAccounts :=
                                      setRewardConfigWrapperSourceFinal_accountMap_equiv
                                        evmDecPost I rescale true
                                    have hAccountsPost := accountMapEquiv.trans
                                      (by simpa [hslotPost] using hIdeal)
                                      (by
                                        simpa [evmDecPost, evmPost, initState, solcSlotWord,
                                          Solm.EVM.storageLoad, State.lookupAccount,
                                          setRewardConfigSlot0Up] using hsourceAccounts)
                                    have hcreated :
                                        cA'' =
                                          (setRewardConfigWrapperSourceFinal evmDecPost I rescale true).createdAccounts := by
                                      simp [setRewardConfigWrapperSourceFinal,
                                        setRewardConfigWrapperSourceAfterShouldUpscale,
                                        setRewardConfigWrapperSourceAfterRescale,
                                        setRewardConfigWrapperSourceAfterToken, evmDecPost,
                                        storageStore_createdAccounts]
                                    exact
                                      (cometRewardsSetRewardConfigX_after_decimals_upscale_success
                                          rdDecPost houtDec32 houtDecSize hdec8Return
                                          hle77Return hsafe64Return hbase64Return hperm
                                          hcanonComet hcanonToken hupLe hbaseZero hrescale)
                                        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                                          hcreated
                                          (by simpa [evmDecPost, hslotPost.symm] using hAccountsPost)
                                          (returnEquiv.fallthrough rfl (by rfl) (by native_decide))
                              · have hgt64 :
                                    2 ^ 64 - 1 <
                                      (10 : ℕ) ^
                                        fromByteArrayBigEndian (outDec.extract 0 32) :=
                                  Nat.lt_of_not_ge hsafe64
                                have hbody :
                                    ExecTransitionBody config contract
                                      (initState cA gh bl σ_solm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      (setRewardConfigStore I)
                                      setRewardConfigTransition.body .reverted := by
                                  exact
                                    cometRewardsSetRewardConfigBodyReverts_safe64Failure
                                      (initState cA gh bl σ_solm σ₀
                                        (Sat256.ofUInt256 g) A I)
                                      evmPost evmDecPost I
                                      (by simp only [initState]; exact hwv)
                                      (by simp only [initState]; exact hhi)
                                      hgovSolm
                                      htokenZeroSolm
                                      (by simpa [evmPost] using hcallS)
                                      hdecBase
                                      (by simpa [evmPost, evmDecPost] using hcallDec)
                                      hdecDecimals
                                      hle77
                                      hgt64
                                have hdec8Return :
                                    (setRewardConfigDecimalsReturnWord outDec).toNat <
                                      EVM.twoPow 8 := by
                                  rw [htoDec]
                                  exact hdecWord
                                have hle77Return :
                                    (setRewardConfigDecimalsReturnWord outDec).toNat ≤ 77 := by
                                  rw [htoDec]
                                  exact hle77
                                have hgt64Return :
                                    2 ^ 64 - 1 <
                                      (10 : ℕ) ^
                                        (setRewardConfigDecimalsReturnWord outDec).toNat := by
                                  rw [htoDec]
                                  exact hgt64
                                exact
                                  (cometRewardsSetRewardConfigX_after_decimals_safe64_revert
                                      rdDecPost houtDec32 houtDecSize hdec8Return hle77Return
                                      hgt64Return)
                                    |>.reEquivExecutionRevert hcode hd hdec hbody
                            · let evmDecPost : EVM.State :=
                                { evmPost with
                                    accountMap := σ''_solm
                                    substate := A''_solm
                                    createdAccounts := cA'' }
                              have houtDecSize : outDec.size < UInt256.size :=
                                lt_size_of_lt_sign houtDecSign
                              have hgt77 :
                                  77 < fromByteArrayBigEndian (outDec.extract 0 32) :=
                                Nat.lt_of_not_ge hle77
                              have hbody :
                                  ExecTransitionBody config contract
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    (setRewardConfigStore I)
                                    setRewardConfigTransition.body .reverted := by
                                exact
                                  cometRewardsSetRewardConfigBodyReverts_pow10Failure
                                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                    evmPost evmDecPost I
                                    (by simp only [initState]; exact hwv)
                                    (by simp only [initState]; exact hhi)
                                    hgovSolm
                                    htokenZeroSolm
                                    (by simpa [evmPost] using hcallS)
                                    hdecBase
                                    (by simpa [evmPost, evmDecPost] using hcallDec)
                                    hdecDecimals
                                    hgt77
                              have hdec8Return :
                                  (setRewardConfigDecimalsReturnWord outDec).toNat <
                                    EVM.twoPow 8 := by
                                rw [htoDec]
                                exact hdecWord
                              have hgt77Return :
                                  77 < (setRewardConfigDecimalsReturnWord outDec).toNat := by
                                rw [htoDec]
                                exact hgt77
                              exact
                                (cometRewardsSetRewardConfigX_after_decimals_pow10_revert
                                    rdDecPost houtDec32 houtDecSize hdec8Return hgt77Return)
                                  |>.reEquivExecutionRevert hcode hd hdec hbody
                          · let evmDecPost : EVM.State :=
                              { evmPost with
                                  accountMap := σ''_solm
                                  substate := A''_solm
                                  createdAccounts := cA'' }
                            have houtDecSize : outDec.size < UInt256.size :=
                              lt_size_of_lt_sign houtDecSign
                            have hdecDecimals :=
                              cometRewardsDecimals_decode_none_noncanon
                                (out := outDec) houtDec32 houtDecSign hdecWord
                            have hbody :
                                ExecTransitionBody config contract
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  (setRewardConfigStore I)
                                  setRewardConfigTransition.body .reverted := by
                              exact
                                cometRewardsSetRewardConfigBodyReverts_decimalsDecodeFailure
                                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                  evmPost evmDecPost I
                                  (by simp only [initState]; exact hwv)
                                  (by simp only [initState]; exact hhi)
                                  hgovSolm
                                  htokenZeroSolm
                                  (by simpa [evmPost] using hcallS)
                                  hdecBase
                                  (by simpa [evmPost, evmDecPost] using hcallDec)
                                  hdecDecimals
                            have hdecNo :
                                ¬ (setRewardConfigDecimalsReturnWord outDec).toNat <
                                  EVM.twoPow 8 := by
                              intro hlt
                              have hto :
                                  (setRewardConfigDecimalsReturnWord outDec).toNat =
                                    fromByteArrayBigEndian (outDec.extract 0 32) := by
                                simpa [setRewardConfigDecimalsReturnWord] using
                                  UInt256.toNat_ofNat_of_lt
                                    (fromByteArrayBigEndian_extract0_32_lt houtDec32)
                              exact hdecWord (by
                                rw [← hto]
                                exact hlt)
                            exact
                              (cometRewardsSetRewardConfigX_after_decimals_noncanon_revert
                                  rdDecPost houtDec32 houtDecSize hdecNo)
                                |>.reEquivExecutionRevert hcode hd hdec hbody
                    · have hdecBase := cometRewardsBaseAccrualScale_decode_none_noncanon
                        (out := out) hout32 houtSign hbaseWord
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (setRewardConfigStore I)
                            setRewardConfigTransition.body .reverted := by
                        exact cometRewardsSetRewardConfigBodyReverts_baseDecodeFailure
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          evmPost I
                          (by simp only [initState]; exact hwv)
                          (by simp only [initState]; exact hhi)
                          hgovSolm
                          htokenZeroSolm
                          (by simpa [evmPost] using hcallS)
                          hdecBase
                      have hbaseNo :
                          ¬ (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64 := by
                        intro hlt
                        have hto :
                            (setRewardConfigBaseReturnWord out).toNat =
                              fromByteArrayBigEndian (out.extract 0 32) := by
                          simpa [setRewardConfigBaseReturnWord] using
                            UInt256.toNat_ofNat_of_lt
                              (fromByteArrayBigEndian_extract0_32_lt hout32)
                        exact hbaseWord (by
                          rw [← hto]
                          exact hlt)
                      exact
                        (cometRewardsSetRewardConfigX_after_baseAccrualScale_noncanon_revert
                            rdPost hout32 houtSize hbaseNo)
                          |>.reEquivExecutionRevert hcode hd hdec hbody
              · rw [not_lt] at hdepth
                have hdepth1024 : I.depth = 1024 := Fin.ext (by
                  have := I.depth.isLt
                  omega)
                let evmInit : EVM.State :=
                  initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                let evmFail : EVM.State :=
                  { evmInit with
                      substate :=
                        (evmInit.addAccessedAccount
                          (EVM.address (AccountAddress.ofNat
                            (setRewardConfigCometWord I).toNat))).substate }
                have hcallS :
                    typedCallViaEVM config evmInit
                      (EVM.address (AccountAddress.ofNat (setRewardConfigCometWord I).toNat))
                      "baseAccrualScale" 0 []
                      (false, evmFail, ByteArray.empty) false := by
                  exact callNotMade_depthLimit
                    (cfg := config) (evm := evmInit)
                    (tgt := EVM.address (AccountAddress.ofNat
                      (setRewardConfigCometWord I).toNat))
                    (name := "baseAccrualScale") (args := [])
                    (calldata := (setRewardConfigWrapperBaseAccrualScaleCalldataMem I)
                      |>.readWithPadding 128 4)
                    (callPerm := false)
                    (setRewardConfigWrapperBaseAccrualScaleCalldataMem_encode I)
                    (by simpa [evmInit, initState] using hdepth1024)
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (setRewardConfigStore I)
                      setRewardConfigTransition.body .reverted := by
                  exact cometRewardsSetRewardConfigBodyReverts_baseCallFailure
                    evmInit evmFail I
                    (by simp only [evmInit, initState]; exact hwv)
                    (by simp only [evmInit, initState]; exact hhi)
                    (by simpa [evmInit] using hgovSolm)
                    (by simpa [evmInit] using htokenZeroSolm)
                    hcallS
                exact (cometRewardsSetRewardConfigX_baseAccrualScale_callDepthLimit
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    hwv hsz68 hsize hhi hcanonComet hcanonToken hauthEq htokenZero hreach
                    hdepth1024)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := cometRewardsDecode_setRewardConfig_none_noncanon_token
            (I := I) hsz68 hhi hcanonComet hcanonToken
          have hnc : UInt256.eq (setRewardConfigTokenWord I)
              (UInt256.land (setRewardConfigTokenWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanonToken (solcAddrCanonical_of_clean he))
          exact (cometRewardsSetRewardConfigX_noncanon_token (g := Sat256.ofUInt256 g)
              hwv hsz68 hsize hhi hcanonComet hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := cometRewardsDecode_setRewardConfig_none_noncanon_comet
          (I := I) hsz68 hhi hcanonComet
        have hnc : UInt256.eq (setRewardConfigCometWord I)
            (UInt256.land (setRewardConfigCometWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanonComet (solcAddrCanonical_of_clean he))
        exact (cometRewardsSetRewardConfigX_noncanon_comet (g := Sat256.ofUInt256 g)
            hwv hsz68 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_setRewardConfig_none_huge (I := I) hbig
      exact (cometRewardsSetRewardConfigX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := cometRewardsDecode_setRewardConfig_none_short (I := I) hsz4 hshort
    exact (cometRewardsSetRewardConfigX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
