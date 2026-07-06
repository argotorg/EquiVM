import Benchmarks.CompoundIII.CometRewards.RewardConfig
import Benchmarks.CompoundIII.CometRewards.TransferGovernor
import Reasoning.ExternalCall
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `setRewardConfigWithMultiplier(address,address,uint256)` -/

abbrev setRewardConfigWithMultiplierCometWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev setRewardConfigWithMultiplierTokenWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev setRewardConfigWithMultiplierMultiplierWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev setRewardConfigWithMultiplierCometValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat)

abbrev setRewardConfigWithMultiplierTokenValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat)

abbrev setRewardConfigWithMultiplierMultiplierValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (setRewardConfigWithMultiplierMultiplierWord I).toNat)

abbrev setRewardConfigWithMultiplierStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "comet" (setRewardConfigWithMultiplierCometValue I)).insert
    "token" (setRewardConfigWithMultiplierTokenValue I)).insert "multiplier"
      (setRewardConfigWithMultiplierMultiplierValue I)

abbrev setRewardConfigWithMultiplierBodyStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "multiplier" (setRewardConfigWithMultiplierMultiplierValue I)).insert
    "token" (setRewardConfigWithMultiplierTokenValue I)).insert "comet"
      (setRewardConfigWithMultiplierCometValue I)

abbrev setRewardConfigWithMultiplierArgs (I : ExecutionEnv) : List Value :=
  [setRewardConfigWithMultiplierCometValue I, setRewardConfigWithMultiplierTokenValue I,
    setRewardConfigWithMultiplierMultiplierValue I]

abbrev setRewardConfigWithMultiplierFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (setRewardConfigWithMultiplierStore I).insert "__calldata"
      (.bytes evm.executionEnv.calldata) }

abbrev setRewardConfigWithMultiplierBodyFrame (_evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := setRewardConfigWithMultiplierBodyStore I }

def setRewardConfigWithMultiplierSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardConfigSlot (.address (AccountAddress.ofNat
    (setRewardConfigWithMultiplierCometWord I).toNat))

theorem setRewardConfigWithMultiplierSlotOf_eq_solc (I : ExecutionEnv)
    (hcanon : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus) :
    setRewardConfigWithMultiplierSlotOf I =
      solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I) := by
  unfold setRewardConfigWithMultiplierSlotOf rewardConfigSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  rfl

theorem setRewardConfigWithMultiplierStore_comet (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierStore I).get? "comet" =
      some (setRewardConfigWithMultiplierCometValue I) := by
  rw [setRewardConfigWithMultiplierStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigWithMultiplierStore_token (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierStore I).get? "token" =
      some (setRewardConfigWithMultiplierTokenValue I) := by
  rw [setRewardConfigWithMultiplierStore, store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigWithMultiplierStore_multiplier (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierStore I).get? "multiplier" =
      some (setRewardConfigWithMultiplierMultiplierValue I) := by
  rw [setRewardConfigWithMultiplierStore, store_get_self]

theorem setRewardConfigWithMultiplierStore_governor (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierStore I).get? "governor" = none := by
  rw [setRewardConfigWithMultiplierStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem setRewardConfigWithMultiplierStore_rewardConfig (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierStore I).get? "rewardConfig" = none := by
  rw [setRewardConfigWithMultiplierStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem setRewardConfigWithMultiplierBodyStore_comet (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierBodyStore I).get? "comet" =
      some (setRewardConfigWithMultiplierCometValue I) := by
  rw [setRewardConfigWithMultiplierBodyStore, store_get_self]

theorem setRewardConfigWithMultiplierBodyStore_token (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierBodyStore I).get? "token" =
      some (setRewardConfigWithMultiplierTokenValue I) := by
  rw [setRewardConfigWithMultiplierBodyStore, store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigWithMultiplierBodyStore_multiplier (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierBodyStore I).get? "multiplier" =
      some (setRewardConfigWithMultiplierMultiplierValue I) := by
  rw [setRewardConfigWithMultiplierBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigWithMultiplierBodyStore_governor (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierBodyStore I).get? "governor" = none := by
  rw [setRewardConfigWithMultiplierBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem setRewardConfigWithMultiplierBodyStore_rewardConfig (I : ExecutionEnv) :
    (setRewardConfigWithMultiplierBodyStore I).get? "rewardConfig" = none := by
  rw [setRewardConfigWithMultiplierBodyStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  native_decide

theorem evalExpr_setRewardConfigWithMultiplier_comet (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm (.var "comet") =
      .ok (setRewardConfigWithMultiplierCometValue I) := by
  simp only [setRewardConfigWithMultiplierFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierStore_comet]

theorem evalExpr_setRewardConfigWithMultiplier_token (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm (.var "token") =
      .ok (setRewardConfigWithMultiplierTokenValue I) := by
  simp only [setRewardConfigWithMultiplierFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierStore_token]

theorem evalExpr_setRewardConfigWithMultiplier_multiplier (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm (.var "multiplier") =
      .ok (setRewardConfigWithMultiplierMultiplierValue I) := by
  simp only [setRewardConfigWithMultiplierFrame, evalExpr?, EvalResult.ofOption]
  rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierStore_multiplier]

theorem evalExprs_setRewardConfigWithMultiplier_args (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? config (setRewardConfigWithMultiplierFrame evm I) evm
      [.var "comet", .var "token", .var "multiplier"] =
        .ok (setRewardConfigWithMultiplierArgs I) := by
  simp only [setRewardConfigWithMultiplierArgs, evalExprs?,
    evalExpr_setRewardConfigWithMultiplier_comet,
    evalExpr_setRewardConfigWithMultiplier_token,
    evalExpr_setRewardConfigWithMultiplier_multiplier, EvalResult.bind, bind]
  rfl

theorem evalExpr_setRewardConfigWithMultiplier_body_comet (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm (.var "comet") =
      .ok (setRewardConfigWithMultiplierCometValue I) := by
  simp only [setRewardConfigWithMultiplierBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigWithMultiplierBodyStore_comet]

theorem evalExpr_setRewardConfigWithMultiplier_body_token (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm (.var "token") =
      .ok (setRewardConfigWithMultiplierTokenValue I) := by
  simp only [setRewardConfigWithMultiplierBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigWithMultiplierBodyStore_token]

theorem evalExpr_setRewardConfigWithMultiplier_body_multiplier (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm (.var "multiplier") =
      .ok (setRewardConfigWithMultiplierMultiplierValue I) := by
  simp only [setRewardConfigWithMultiplierBodyFrame, evalExpr?, EvalResult.ofOption]
  rw [setRewardConfigWithMultiplierBodyStore_multiplier]

theorem bindParams_setRewardConfigWithMultiplier (I : ExecutionEnv) :
    bindParams? setRewardConfigWithMultiplierFunction.params
      (setRewardConfigWithMultiplierArgs I) =
        some (setRewardConfigWithMultiplierBodyStore I) := by
  simp [setRewardConfigWithMultiplierFunction, setRewardConfigWithMultiplierArgs,
    setRewardConfigWithMultiplierCometValue, setRewardConfigWithMultiplierTokenValue,
    setRewardConfigWithMultiplierMultiplierValue, setRewardConfigWithMultiplierBodyStore,
    bindParams?]

theorem lookupCallable_setRewardConfigWithMultiplierBody :
    lookupCallable? contract "setRewardConfigWithMultiplierBody" =
      some setRewardConfigWithMultiplierFunction.toCallable := by
  rfl

theorem lookupCallable_pow10 :
    lookupCallable? contract "pow10" = some pow10Function.toCallable := by
  rfl

theorem lookupCallable_safe64 :
    lookupCallable? contract "safe64" = some safe64Function.toCallable := by
  rfl

abbrev pow10Store (n : ℕ) : Store :=
  (∅ : Store).insert "n" (.int (Int.ofNat n))

abbrev safe64Store (n : ℕ) : Store :=
  (∅ : Store).insert "n" (.int (Int.ofNat n))

theorem bindParams_pow10 (n : ℕ) :
    bindParams? pow10Function.params [.int (Int.ofNat n)] = some (pow10Store n) := by
  simp [pow10Function, pow10Store, bindParams?]

theorem bindParams_safe64 (n : ℕ) :
    bindParams? safe64Function.params [.int (Int.ofNat n)] = some (safe64Store n) := by
  simp [safe64Function, safe64Store, bindParams?]

theorem evalExpr_pow10_bound_false (evm : EVM.State) {n : ℕ} (hgt : 77 < n) :
    evalExpr? config { contract := contract, locals := pow10Store n } evm
      (.binary .le (.var "n") (.intLit 77)) = .ok (.bool false) := by
  have hle : ¬ Int.ofNat n ≤ (77 : Int) := by
    intro hn
    have hnNat : n ≤ 77 := Int.ofNat_le.mp hn
    omega
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pow10Store]
  rw [store_get_self]
  simp [evalBinaryOp?]
  exact hgt

theorem pow10FunctionBodyReverts_gt77 (evm : EVM.State) {n : ℕ} (hgt : 77 < n) :
    ExecFuncBody config { contract := contract, locals := pow10Store n } evm
      pow10Function.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [pow10Function] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_pow10_bound_false evm hgt))

theorem evalExpr_pow10_bound_true (evm : EVM.State) {n : ℕ} (hle : n ≤ 77) :
    evalExpr? config { contract := contract, locals := pow10Store n } evm
      (.binary .le (.var "n") (.intLit 77)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pow10Store]
  rw [store_get_self]
  simp [evalBinaryOp?]
  exact hle

theorem evalExpr_pow10_return (evm : EVM.State) {n : ℕ} (hle : n ≤ 77) :
    evalExpr? config { contract := contract, locals := pow10Store n } evm
      (u256 (.binary .exp (.intLit 10) (.var "n"))) =
      .ok (.int ((10 : Int) ^ n)) := by
  simp only [u256, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pow10Store]
  rw [store_get_self]
  simp [evalBinaryOp?]
  rw [if_neg (by omega)]
  simp only [uint256Int]
  have hpowNat : (10 : ℕ) ^ n ≤ 10 ^ 77 :=
    Nat.pow_le_pow_right (by norm_num) hle
  have hbound : (10 : ℕ) ^ n < 2 ^ 256 :=
    lt_of_le_of_lt hpowNat (by norm_num)
  rw [if_neg]
  · rfl
  · push Not
    constructor
    · positivity
    · exact_mod_cast hbound

theorem pow10FunctionBodyReturns_le77 (evm : EVM.State) {n : ℕ} (hle : n ≤ 77) :
    ExecFuncBody config { contract := contract, locals := pow10Store n } evm
      pow10Function.body
      (.returned { contract := contract, locals := pow10Store n } evm
        (some [.int ((10 : Int) ^ n)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [pow10Function] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_pow10_bound_true evm hle))
      (ExecBlock.consReturn
        (ExecStmt.return (by
          simp [evalExprs?, evalExpr_pow10_return evm hle, EvalResult.bind, bind]
          rfl)))

theorem evalExpr_safe64_bound_false (evm : EVM.State) {n : ℕ}
    (hgt : 2 ^ 64 - 1 < n) :
    evalExpr? config { contract := contract, locals := safe64Store n } evm
      (.binary .le (.var "n") (.intLit maxUint64)) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, safe64Store]
  rw [store_get_self]
  simp [evalBinaryOp?, maxUint64]
  exact hgt

theorem evalExpr_safe64_bound_true (evm : EVM.State) {n : ℕ}
    (hle : n ≤ 2 ^ 64 - 1) :
    evalExpr? config { contract := contract, locals := safe64Store n } evm
      (.binary .le (.var "n") (.intLit maxUint64)) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, safe64Store]
  rw [store_get_self]
  simp [evalBinaryOp?, maxUint64]
  exact hle

theorem evalExpr_safe64_return (evm : EVM.State) {n : ℕ} (hle : n ≤ 2 ^ 64 - 1) :
    evalExpr? config { contract := contract, locals := safe64Store n } evm
      (u64 (.var "n")) = .ok (.int (Int.ofNat n)) := by
  simp only [u64, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, safe64Store]
  rw [store_get_self]
  simp [uint64Int]
  rw [if_neg]
  · rfl
  · push Not
    constructor
    · omega
    · exact Nat.lt_succ_of_le hle

theorem safe64FunctionBodyReverts_gt (evm : EVM.State) {n : ℕ}
    (hgt : 2 ^ 64 - 1 < n) :
    ExecFuncBody config { contract := contract, locals := safe64Store n } evm
      safe64Function.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [safe64Function] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse (evalExpr_safe64_bound_false evm hgt))

theorem safe64FunctionBodyReturns_le (evm : EVM.State) {n : ℕ}
    (hle : n ≤ 2 ^ 64 - 1) :
    ExecFuncBody config { contract := contract, locals := safe64Store n } evm
      safe64Function.body
      (.returned { contract := contract, locals := safe64Store n } evm
        (some [.int (Int.ofNat n)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [safe64Function] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue (evalExpr_safe64_bound_true evm hle))
      (ExecBlock.consReturn
        (ExecStmt.return (by
          simp [evalExprs?, evalExpr_safe64_return evm hle, EvalResult.bind, bind]
          rfl)))

theorem evalExpr_setRewardConfigWithMultiplier_governor (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm (.storage governorRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (setRewardConfigWithMultiplierFrame evm I) evm
      governorRef = .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((setRewardConfigWithMultiplierStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "governor" = none
      rw [store_get_ne _ _ (by decide)]
      exact setRewardConfigWithMultiplierStore_governor I)
    (her := her) (hty := hty) (hloc := by rfl),
    cometRewardsStorageLocLoad_address_offset0]

theorem evalExpr_setRewardConfigWithMultiplier_body_governor (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm (.storage governorRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      governorRef = .ok { base := "governor", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, governorRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage
      ({ base := "governor", steps := [] } : EvaledStorageRef) = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar
    (hbase := by
      change (setRewardConfigWithMultiplierBodyStore I).get? "governor" = none
      exact setRewardConfigWithMultiplierBodyStore_governor I)
    (her := her) (hty := hty) (hloc := by rfl),
    cometRewardsStorageLocLoad_address_offset0]

theorem evalExpr_setRewardConfigWithMultiplier_sender (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setRewardConfigWithMultiplier_body_sender (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_setRewardConfigWithMultiplier_auth_true (evm : EVM.State)
    (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_sender,
    evalExpr_setRewardConfigWithMultiplier_governor, bind, EvalResult.bind, evalBinaryOp?]
  rw [solcMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) hgov]
  simp [BEq.beq]

theorem evalExpr_setRewardConfigWithMultiplier_body_auth_true (evm : EVM.State)
    (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_body_sender,
    evalExpr_setRewardConfigWithMultiplier_body_governor, bind, EvalResult.bind, evalBinaryOp?]
  rw [solcMaskedAddress_eq_source_of_word_eq (I := evm.executionEnv) hgov]
  simp [BEq.beq]

theorem evalExpr_setRewardConfigWithMultiplier_auth_false (evm : EVM.State)
    (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_sender,
    evalExpr_setRewardConfigWithMultiplier_governor, bind, EvalResult.bind, evalBinaryOp?]
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

theorem evalExpr_setRewardConfigWithMultiplier_body_auth_false (evm : EVM.State)
    (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (.binary .eq sender (.storage governorRef)) = .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_body_sender,
    evalExpr_setRewardConfigWithMultiplier_body_governor, bind, EvalResult.bind, evalBinaryOp?]
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

theorem evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef config (setRewardConfigWithMultiplierFrame evm I) evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (setRewardConfigWithMultiplierCometWord I).toNat)),
                        .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierStore_comet]

theorem evalStorageRef_setRewardConfigWithMultiplier_body_rewardConfig_field
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (setRewardConfigWithMultiplierCometWord I).toNat)),
                        .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [setRewardConfigWithMultiplierBodyStore_comet]

theorem evalExpr_setRewardConfigWithMultiplier_rewardConfig_token (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm
      (.storage (rewardConfigF (.var "comet") "token")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigWithMultiplierSlotOf I))
            solcAddrMask).toNat)) := by
  have her := evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field evm I "token"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigWithMultiplierCometWord I).toNat)),
                  .field "token"] } =
      some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigWithMultiplierCometWord I).toNat)),
                  .field "token"] } =
      fun _ => some (fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 0
        20 (by decide) .address) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((setRewardConfigWithMultiplierStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardConfig" = none
      rw [store_get_ne _ _ (by decide)]
      exact setRewardConfigWithMultiplierStore_rewardConfig I)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_address_offset0 evm
    (setRewardConfigWithMultiplierSlotOf I)

theorem evalExpr_setRewardConfigWithMultiplier_body_rewardConfig_token (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (.storage (rewardConfigF (.var "comet") "token")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigWithMultiplierSlotOf I))
            solcAddrMask).toNat)) := by
  have her := evalStorageRef_setRewardConfigWithMultiplier_body_rewardConfig_field evm I "token"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigWithMultiplierCometWord I).toNat)),
                  .field "token"] } =
      some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat
                    (setRewardConfigWithMultiplierCometWord I).toNat)),
                  .field "token"] } =
      fun _ => some (fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 0
        20 (by decide) .address) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change (setRewardConfigWithMultiplierBodyStore I).get? "rewardConfig" = none
      exact setRewardConfigWithMultiplierBodyStore_rewardConfig I)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_address_offset0 evm
    (setRewardConfigWithMultiplierSlotOf I)

theorem evalExpr_setRewardConfigWithMultiplier_zeroAddr (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem evalExpr_setRewardConfigWithMultiplier_body_zeroAddr (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption,
    pure, bind]

theorem evalExpr_setRewardConfigWithMultiplier_token_zero_true (evm : EVM.State)
    (I : ExecutionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩) :
    evalExpr? config (setRewardConfigWithMultiplierFrame evm I) evm
      (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr) =
        .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_rewardConfig_token,
    evalExpr_setRewardConfigWithMultiplier_zeroAddr, bind, EvalResult.bind, evalBinaryOp?]
  rw [htoken]
  simp [BEq.beq]

theorem evalExpr_setRewardConfigWithMultiplier_body_token_zero_true (evm : EVM.State)
    (I : ExecutionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr) =
        .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_body_rewardConfig_token,
    evalExpr_setRewardConfigWithMultiplier_body_zeroAddr, bind, EvalResult.bind, evalBinaryOp?]
  rw [htoken]
  simp [BEq.beq]

theorem accountAddress_ofNat_masked_ne_zero_of_ne (w : UInt256)
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

theorem evalExpr_setRewardConfigWithMultiplier_body_token_zero_false (evm : EVM.State)
    (I : ExecutionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    evalExpr? config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      (.binary .eq (.storage (rewardConfigF (.var "comet") "token")) zeroAddr) =
        .ok (.bool false) := by
  simp only [evalExpr?, evalExpr_setRewardConfigWithMultiplier_body_rewardConfig_token,
    evalExpr_setRewardConfigWithMultiplier_body_zeroAddr, bind, EvalResult.bind, evalBinaryOp?]
  have haddr := accountAddress_ofNat_masked_ne_zero_of_ne
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (setRewardConfigWithMultiplierSlotOf I)) htoken
  rw [show ((.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigWithMultiplierSlotOf I))
            solcAddrMask).toNat) : Value) ==
        .address (AccountAddress.ofNat 0)) = false by
    simp [BEq.beq, haddr]]

theorem setRewardConfigWithMultiplierFunctionBodyReverts_auth
    (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [setRewardConfigWithMultiplierFunction] using
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_setRewardConfigWithMultiplier_body_auth_false evm I hgov))

theorem setRewardConfigWithMultiplierFunctionBodyReverts_configured
    (evm : EVM.State) (I : ExecutionEnv)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [setRewardConfigWithMultiplierFunction] using
    ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov))
      (ExecBlock.consRevert
        (ExecStmt.requireFalse
          (evalExpr_setRewardConfigWithMultiplier_body_token_zero_false evm I htoken)))

theorem setRewardConfigWithMultiplierFunctionBodyReverts_baseCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (false, evm', out) false) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (cfg := config) (evm := evm) (evm' := evm')
      (solm := { contract := contract, locals := setRewardConfigWithMultiplierBodyStore I })
      (receiver := .var "comet") (retVar := "accrualScale") (name := "baseAccrualScale")
      (target := AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat)
      (eth := .intLit 0) (sendVal := 0) (args := []) (argVals := []) (out := out)
      (perm := false)
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcall)

theorem setRewardConfigWithMultiplierFunctionBodyReverts_baseDecodeFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "baseAccrualScale" out = none) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcall hdec)

theorem setRewardConfigWithMultiplierFunctionBodyReverts_decimalsCallFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (false, evmDec, decOut) false) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (cfg := config) (evm := evmBase) (evm' := evmDec)
      (solm :=
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue })
      (receiver := .var "token") (retVar := "tokenDecimals") (name := "decimals")
      (target := AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat)
      (eth := .intLit 0) (sendVal := 0) (args := []) (argVals := []) (out := decOut)
      (perm := false)
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec)

theorem setRewardConfigWithMultiplierFunctionBodyReverts_decimalsDecodeFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = none) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      htokenExpr
      (by simp [evalExpr?, pure])
        (by rfl)
        hcallDec hdecDec)

theorem setRewardConfigWithMultiplierFunctionBodyReverts_pow10Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hgt : 77 < decNat) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  let afterDecimals : Frame :=
    { contract := contract,
      locals :=
        ((setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue).insert
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

theorem setRewardConfigWithMultiplierFunctionBodyReverts_safe64Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hgt64 : 2 ^ 64 - 1 < (10 : ℕ) ^ decNat) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  let afterDecimals : Frame :=
    { contract := contract,
      locals :=
        ((setRewardConfigWithMultiplierBodyStore I).insert "accrualScale" baseValue).insert
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

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_auth
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask ≠
        solcSourceWord evm.executionEnv) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_auth evm I hgov)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_configured
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_configured evm I hgov htoken)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseCallFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (false, evm', out) false) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_baseCallFailure
            evm evm' I hgov htoken hcall)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseDecodeFailure
    (evm evm' : EVM.State) (I : ExecutionEnv) {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evm', out) false)
    (hdec : config.externalABI.decode? "baseAccrualScale" out = none) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_baseDecodeFailure
            evm evm' I hgov htoken hcall hdec)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_decimalsCallFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (false, evmDec, decOut) false) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_decimalsCallFailure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_decimalsDecodeFailure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec : config.externalABI.decode? "decimals" decOut = none) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_decimalsDecodeFailure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
      (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
        simp [evalExpr?, envValue, pure])).requireStep
          (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
            (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_pow10Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hgt : 77 < decNat) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_pow10Failure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec hgt)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_safe64Failure
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseValue : Value} {decNat : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase : config.externalABI.decode? "baseAccrualScale" baseOut = some [baseValue])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hgt64 : 2 ^ 64 - 1 < (10 : ℕ) ^ decNat) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_safe64Failure
            evm evmBase evmDec I hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hgt64)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

theorem cometRewardsDecode_setRewardConfigWithMultiplier_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (setRewardConfigWithMultiplierTransition.params.map Param.name)
      (transitionSignature setRewardConfigWithMultiplierTransition).paramTypes I.calldata =
        some (setRewardConfigWithMultiplierStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token", "multiplier"]
    [addr, addr, uint256] I.calldata = _
  change decodeCalldata ["comet", "token", "multiplier"]
      [.elem .address, .elem .address, abiUInt256] I.calldata =
    some ((((∅ : Store).insert "comet"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))).insert "token"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))).insert
        "multiplier" (.int (Int.ofNat (calldataWord I.calldata 68).toNat)))
  exact decodeCalldata_address_address_uint256_ok (cd := I.calldata)
    (x := "comet") (y := "token") (z := "multiplier") hsz100 hbig hcanonComet
    hcanonToken

theorem cometRewardsDecode_setRewardConfigWithMultiplier_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode
      (setRewardConfigWithMultiplierTransition.params.map Param.name)
      (transitionSignature setRewardConfigWithMultiplierTransition).paramTypes I.calldata =
        none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token", "multiplier"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["comet", "token", "multiplier"]
      [.elem .address, .elem .address, abiUInt256] I.calldata = none
  exact decodeCalldata_address_address_uint256_none_short
    (cd := I.calldata) (x := "comet") (y := "token") (z := "multiplier") hsz4 hshort

theorem cometRewardsDecode_setRewardConfigWithMultiplier_none_noncanon_comet
    {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncComet : ¬ (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (setRewardConfigWithMultiplierTransition.params.map Param.name)
      (transitionSignature setRewardConfigWithMultiplierTransition).paramTypes I.calldata =
        none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token", "multiplier"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["comet", "token", "multiplier"]
      [.elem .address, .elem .address, abiUInt256] I.calldata = none
  simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "comet") (y := "token") (z := "multiplier") hsz100
      hbig hncComet

theorem cometRewardsDecode_setRewardConfigWithMultiplier_none_noncanon_token
    {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonComet : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hncToken : ¬ (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode
      (setRewardConfigWithMultiplierTransition.params.map Param.name)
      (transitionSignature setRewardConfigWithMultiplierTransition).paramTypes I.calldata =
        none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token", "multiplier"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["comet", "token", "multiplier"]
      [.elem .address, .elem .address, abiUInt256] I.calldata = none
  simpa [setRewardConfigWithMultiplierCometWord, setRewardConfigWithMultiplierTokenWord,
    calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "comet") (y := "token") (z := "multiplier") hsz100
      hbig hcanonComet hncToken

theorem cometRewardsDecode_setRewardConfigWithMultiplier_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (setRewardConfigWithMultiplierTransition.params.map Param.name)
      (transitionSignature setRewardConfigWithMultiplierTransition).paramTypes I.calldata =
        none := by
  show decodeCalldataWithMode config.abiDecodeMode ["comet", "token", "multiplier"]
    [addr, addr, uint256] I.calldata = none
  change decodeCalldata ["comet", "token", "multiplier"]
      [.elem .address, .elem .address, abiUInt256] I.calldata = none
  exact decodeCalldata_address_address_uint256_none_huge
    (cd := I.calldata) (x := "comet") (y := "token") (z := "multiplier") hbig

theorem cometRewardsSetRewardConfigWithMultiplierSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 10)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 10) rfl hsel

theorem cometRewardsDispatch_setRewardConfigWithMultiplier {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 10 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some setRewardConfigWithMultiplierTransition := by
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition,
      rewardConfigTransition, rewardsClaimedTransition, setRewardConfigTransition])
    (post := [setRewardsClaimedTransition, transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, setRewardConfigWithMultiplierSelectorBytes]; exact hsel)
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 10 :=
    (byteArray_eq_of_beq hsel).symm
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [selectorOf, setRewardConfigSelectorBytes, hcd]
    decide

theorem cometRewardsSetRewardConfigWithMultiplierCalldataCheckOk {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
      (by simpa using hsz100) hhi hsize

theorem cometRewardsSetRewardConfigWithMultiplierCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  simpa using
    solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
      hsz4 (by simpa using hshort) hsize (by norm_num)

theorem cometRewardsSetRewardConfigWithMultiplierCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨96⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨96⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  simpa using
    solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
      hbig hsize (by norm_num)

theorem cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2875⟩
      [UInt256.ofNat I.calldata.size, ⟨173⟩, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd159⟩ := hreach
  have rd161 := evm_run rd159 with [jumpdest, callvalue]
  rw [hwv] at rd161
  have rd172 := evm_run rd161 with [
    push2 ⟨797⟩, jumpiNT (by decide),
    push2 ⟨173⟩, calldatasize, push2 ⟨2875⟩]
  exact ⟨_, _, evm_run rd172 with [jump (by native_decide)]⟩

theorem cometRewardsSetRewardConfigWithMultiplierX_shortarg
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigWithMultiplierCalldataCheckShort
    (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  exact evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiT (by decide) (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsSetRewardConfigWithMultiplierX_hugearg
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigWithMultiplierCalldataCheckHuge
    (I := I) hsize hbig
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  exact evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiT (by decide) (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_dec173_args
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨173⟩
      [setRewardConfigWithMultiplierMultiplierWord I,
        setRewardConfigWithMultiplierTokenWord I,
        setRewardConfigWithMultiplierCometWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsSetRewardConfigWithMultiplierCalldataCheckOk
    (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  have rd2909 := evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask =
            setRewardConfigWithMultiplierCometWord I := by
        exact solcAddrMask_clean (by
          simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hcanon0)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    swap2]
  have rd2922 := evm_run rd2909 with [
    push1 ⟨36⟩, calldataload, swap1, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land (setRewardConfigWithMultiplierTokenWord I) solcAddrMask =
            setRewardConfigWithMultiplierTokenWord I := by
        exact solcAddrMask_clean (by
          simpa [setRewardConfigWithMultiplierTokenWord, calldataWord] using hcanon1)
      have hclean' :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨36⟩ : UInt256).toNat 32) := by
        simpa [setRewardConfigWithMultiplierTokenWord, calldataWord] using hclean
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean']
      exact u256_sub_self _),
    swap1]
  have rd2927 := evm_run rd2922 with [
    push1 ⟨68⟩, calldataload, swap1]
  exact ⟨_, _, evm_run rd2927 with [jump (by native_decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_noncanon_comet
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (setRewardConfigWithMultiplierCometWord I)
      (UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigWithMultiplierCalldataCheckOk
    (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  exact evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
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
            UInt256.eq (setRewardConfigWithMultiplierCometWord I)
                (UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask) =
              ⟨1⟩ := by
          simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_noncanon_token
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (setRewardConfigWithMultiplierTokenWord I)
      (UInt256.land (setRewardConfigWithMultiplierTokenWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsSetRewardConfigWithMultiplierCalldataCheckOk
    (I := I) hsz100 hsize hhi
  obtain ⟨_, _, rd2875⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec2875_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hreach
  have rd2884 := evm_run rd2875 with [
    jumpdest, push1 ⟨96⟩, swap1, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2884
  rw [hslt] at rd2884
  have rd2888 := evm_run rd2884 with [
    push2 ⟨1004⟩, jumpiNT (by decide)]
  have rd2909 := evm_run rd2888 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, push1 ⟨4⟩, calldataload, dup3, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
              (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
              solcAddrMask =
            uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        have hclean' :
            UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask =
              setRewardConfigWithMultiplierCometWord I := by
          exact solcAddrMask_clean (by
            simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hcanon0)
        simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hclean'
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    swap2]
  exact evm_run rd2909 with [
    push1 ⟨36⟩, calldataload, swap1, dup2, and, dup2, sub,
    push2 ⟨1004⟩,
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
            UInt256.eq (setRewardConfigWithMultiplierTokenWord I)
                (UInt256.land (setRewardConfigWithMultiplierTokenWord I) solcAddrMask) =
              ⟨1⟩ := by
          simpa [setRewardConfigWithMultiplierTokenWord, calldataWord] using hraw
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_revert_auth
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd173⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec173_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz100 hsize hhi hcanon0 hcanon1 hreach
  have rd189 := evm_run rd173 with [
    jumpdest, swap2, swap3, swap1, swap4,
    push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, swap4, dup5, push1 ⟨0⟩]
  obtain ⟨_, _, rd190₀⟩ := rd189.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd190⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨190⟩
      [governorWord σ I,
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I,
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd190₀⟩
  have rd193₀ := evm_run rd190 with [and, caller, sub]
  have rd193 := rd193₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd193
  have hsub : UInt256.sub (solcSourceWord I) (governorReturnWord σ I) ≠ ⟨0⟩ := by
    exact u256_sub_ne_zero_of_ne (by
      intro h
      exact hauth h.symm)
  have hsub' :
      UInt256.sub (UInt256.ofNat I.source.val) (UInt256.land (governorWord σ I) solcAddrMask) ≠
        ⟨0⟩ := by
    simpa [solcSourceWord, governorReturnWord] using hsub
  exact evm_run rd193 with [
    push2 ⟨775⟩, jumpiT hsub' (by native_decide),
    jumpdest, dup7,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨431085831⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem transferGovernorUnauthorizedSelector)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    caller, dup2, dup6, add,
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
theorem cometRewardsSetRewardConfigWithMultiplierX_auth_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨197⟩
      [setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, solcAddrMask,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd173⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_dec173_args
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz100 hsize hhi hcanon0 hcanon1 hreach
  have rd189 := evm_run rd173 with [
    jumpdest, swap2, swap3, swap1, swap4,
    push1 ⟨1⟩, dup1, push1 ⟨160⟩, shl, sub, swap4, dup5, push1 ⟨0⟩]
  obtain ⟨_, _, rd190₀⟩ := rd189.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd190⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨190⟩
      [governorWord σ I,
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I,
        UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [governorWord] using rd190₀⟩
  have rd193₀ := evm_run rd190 with [and, caller, sub]
  have rd193 := rd193₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd193
  have hsub :
      UInt256.sub (UInt256.ofNat I.source.val)
        (UInt256.land (governorWord σ I) solcAddrMask) = ⟨0⟩ := by
    have hgov :
        UInt256.land (governorWord σ I) solcAddrMask = UInt256.ofNat I.source.val := by
      simpa [governorReturnWord, solcSourceWord] using hauth
    rw [hgov]
    exact u256_sub_self _
  rw [hsub] at rd193
  exact ⟨_, _, evm_run rd193 with [push2 ⟨775⟩, jumpiNT (by decide)]⟩

def setRewardConfigAlreadyConfiguredSelector : UInt256 :=
  UInt256.shiftLeft (⟨977536693⟩ : UInt256) ⟨224⟩

noncomputable def setRewardConfigAlreadyConfiguredSelectorMem (comet : UInt256) : ByteArray :=
  (UInt256.toByteArray setRewardConfigAlreadyConfiguredSelector).write 0
    (rewardConfigHashMem comet) 128 32

noncomputable def setRewardConfigAlreadyConfiguredMem (comet : UInt256) : ByteArray :=
  (UInt256.toByteArray comet).write 0
    (setRewardConfigAlreadyConfiguredSelectorMem comet) 132 32

def setRewardConfigBaseAccrualScaleSelectorShifted : UInt256 :=
  UInt256.shiftLeft (⟨1359440587⟩ : UInt256) ⟨225⟩

noncomputable def setRewardConfigBaseAccrualScaleCalldataMem (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray setRewardConfigBaseAccrualScaleSelectorShifted).write 0
    (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I)) 128 32

theorem setRewardConfigBaseAccrualScaleCalldataMem_read128_4 (I : ExecutionEnv) :
    (setRewardConfigBaseAccrualScaleCalldataMem I).readWithPadding 128 4 =
      baseAccrualScaleSelector := by
  unfold setRewardConfigBaseAccrualScaleCalldataMem
  rw [toByteArray_write_read_window_of_gap
    (b := setRewardConfigBaseAccrualScaleSelectorShifted)
    (mem := rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
    (off := 128) (start := 0) (len := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))]
  native_decide

theorem setRewardConfigBaseAccrualScaleCalldataMem_encode (I : ExecutionEnv) :
    config.externalABI.encode? "baseAccrualScale" [] =
      some ((setRewardConfigBaseAccrualScaleCalldataMem I).readWithPadding 128 4) := by
  rw [setRewardConfigBaseAccrualScaleCalldataMem_read128_4]
  rfl

abbrev setRewardConfigBasePostCallTail (I : ExecutionEnv) : List UInt256 :=
  [setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
    setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
    setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]

abbrev setRewardConfigBasePostCallStack (z : Bool) (I : ExecutionEnv) : List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: setRewardConfigBasePostCallTail I

noncomputable abbrev setRewardConfigBasePostCallMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (setRewardConfigBaseAccrualScaleCalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev setRewardConfigBasePostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
      (⟨4⟩ : UInt256).toNat)
    (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

theorem setRewardConfigBaseTarget_eq_targetWord (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat) =
      AccountAddress.ofUInt256 (setRewardConfigWithMultiplierCometWord I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat
    (setRewardConfigWithMultiplierCometWord I).toNat).isLt

theorem setRewardConfigBaseAccrualScaleCalldataMem_read64 (I : ExecutionEnv) :
    (setRewardConfigBaseAccrualScaleCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold setRewardConfigBaseAccrualScaleCalldataMem
  rw [toByteArray_write_read_below_of_gap
    (b := setRewardConfigBaseAccrualScaleSelectorShifted)
    (mem := rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
    (off := 128) (read := 64)
    (by have hsz := rewardConfigHashMem_size (setRewardConfigWithMultiplierCometWord I); omega)
    (by norm_num)
    (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))]
  exact rewardConfigHashMem_read64 (setRewardConfigWithMultiplierCometWord I)

theorem setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 (I : ExecutionEnv) :
    128 ≤ (setRewardConfigBaseAccrualScaleCalldataMem I).size := by
  unfold setRewardConfigBaseAccrualScaleCalldataMem
  have h160 :=
    toByteArray_write_size_ge_off_add32 setRewardConfigBaseAccrualScaleSelectorShifted
      (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I)) 128
      (by rw [rewardConfigHashMem_size]; exact lt_usize 32 (by norm_num))
  omega

theorem setRewardConfigBasePostCallLen_le_out_size {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
  by_cases houtSmall : out.size < 32
  · have hnotle : ¬ (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      intro hle
      have hlev : (32 : Nat) ≤ (UInt256.ofNat out.size).toNat := by
        simpa [UInt256.toNat] using hle
      rw [UInt256.toNat_ofNat_of_lt houtSize] at hlev
      omega
    simp [min, hnotle, UInt256.toNat_ofNat_of_lt houtSize]
  · have hle : (⟨32⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change (⟨32⟩ : UInt256).val ≤ (UInt256.ofNat out.size).val
      change (32 : Nat) ≤ (UInt256.ofNat out.size).toNat
      rw [UInt256.toNat_ofNat_of_lt houtSize]
      omega
    simp [min, hle]
    change (32 : Nat) ≤ out.size
    omega

theorem setRewardConfigBasePostCallMem_read64 (I : ExecutionEnv) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (setRewardConfigBasePostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  dsimp [setRewardConfigBasePostCallMem]
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigBaseAccrualScaleCalldataMem_read64 I
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
      exact setRewardConfigBasePostCallLen_le_out_size houtSize
    rw [write_read_below_gen_extend out (setRewardConfigBaseAccrualScaleCalldataMem I)
      128 (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat 64
      hlen hsrc (setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I)
      (by norm_num)]
    exact setRewardConfigBaseAccrualScaleCalldataMem_read64 I

theorem setRewardConfigBasePostCallMem_size_ge128 (I : ExecutionEnv) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    128 ≤ (setRewardConfigBasePostCallMem I out).size := by
  dsimp [setRewardConfigBasePostCallMem]
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat ≤ out.size := by
      exact setRewardConfigBasePostCallLen_le_out_size houtSize
    let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat
    let base := setRewardConfigBaseAccrualScaleCalldataMem I
    have hdest : 128 ≤ base.size := setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I
    by_cases hin : 128 + len ≤ base.size
    · rw [write_eq_gen out base 128 len (by simpa [len] using hlen) (by simpa [len] using hsrc)
        hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < 128 + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 len (by simpa [len] using hlen)
        (by simpa [len] using hsrc) hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem setRewardConfigBasePostCallMem_mload64 (I : ExecutionEnv) {out : ByteArray}
    (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setRewardConfigBasePostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigBasePostCallAw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
          ((setRewardConfigBasePostCallMem I out).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  apply mloadFreePtrValue
  · exact lt_of_lt_of_le (by norm_num) (setRewardConfigBasePostCallMem_size_ge128 I houtSize)
  · native_decide
  · exact setRewardConfigBasePostCallMem_read64 I houtSize

def uint64Mask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩

def uint8Int : IntType := .uint ⟨8, by decide⟩

def uint8 : ABIType := .elem (.int uint8Int)

theorem uint64Mask_toNat : uint64Mask.toNat = 2 ^ 64 - 1 := by
  native_decide

theorem uint64Mask_clean {w : UInt256} (h64 : w.toNat < EVM.twoPow 64) :
    UInt256.land w uint64Mask = w := by
  apply u256_inj
  show (UInt256.land w uint64Mask).toNat = w.toNat
  have h64' : w.toNat < 2 ^ 64 := by
    simpa [EVM.twoPow] using h64
  rw [u256_land_toNat, uint64Mask_toNat, nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt h64']
  exact Nat.mod_eq_of_lt w.val.isLt

theorem uint64Mask_not_clean {w : UInt256} (h64 : ¬ w.toNat < EVM.twoPow 64) :
    UInt256.land w uint64Mask ≠ w := by
  intro hclean
  have hto := congrArg UInt256.toNat hclean
  have hsmall : w.toNat % 2 ^ 64 < UInt256.size := by
    have hmod := Nat.mod_lt w.toNat (by norm_num : 0 < 2 ^ 64)
    have hsz : UInt256.size = 2 ^ 256 := by decide
    omega
  rw [u256_land_toNat, uint64Mask_toNat, nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt hsmall] at hto
  have hlt := Nat.mod_lt w.toNat (by norm_num : 0 < 2 ^ 64)
  rw [hto] at hlt
  exact h64 (by simpa [EVM.twoPow] using hlt)

def uint8Mask : UInt256 := ⟨255⟩

theorem uint8Mask_toNat : uint8Mask.toNat = 2 ^ 8 - 1 := by
  native_decide

theorem uint8Mask_clean {w : UInt256} (h8 : w.toNat < EVM.twoPow 8) :
    UInt256.land w uint8Mask = w := by
  apply u256_inj
  show (UInt256.land w uint8Mask).toNat = w.toNat
  have h8' : w.toNat < 2 ^ 8 := by
    simpa [EVM.twoPow] using h8
  rw [u256_land_toNat, uint8Mask_toNat, nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt h8']
  exact Nat.mod_eq_of_lt w.val.isLt

theorem uint8Mask_not_clean {w : UInt256} (h8 : ¬ w.toNat < EVM.twoPow 8) :
    UInt256.land w uint8Mask ≠ w := by
  intro hclean
  have hto := congrArg UInt256.toNat hclean
  have hsmall : w.toNat % 2 ^ 8 < UInt256.size := by
    have hmod := Nat.mod_lt w.toNat (by norm_num : 0 < 2 ^ 8)
    have hsz : UInt256.size = 2 ^ 256 := by decide
    omega
  rw [u256_land_toNat, uint8Mask_toNat, nat_land_mask_eq_mod,
    Nat.mod_eq_of_lt hsmall] at hto
  have hlt := Nat.mod_lt w.toNat (by norm_num : 0 < 2 ^ 8)
  rw [hto] at hlt
  exact h8 (by simpa [EVM.twoPow] using hlt)

def setRewardConfigUInt64Offset20Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
    (UInt256.land (UInt256.shiftLeft val ⟨160⟩)
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)))

def setRewardConfigBoolOffset28Word (old bit : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)))
    (UInt256.land (UInt256.shiftLeft bit ⟨224⟩)
      (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩))

theorem setRewardConfigUInt64Offset20Nat_lt_size (old val : UInt256) :
    old.toNat % 2 ^ 160 + 2 ^ 160 * (val.toNat % 2 ^ 64) +
      2 ^ 224 * (old.toNat / 2 ^ 224) < UInt256.size := by
  have h0 : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
  have h1 : val.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have h2 : old.toNat / 2 ^ 224 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have h0le : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt h0
  have h1le : val.toNat % 2 ^ 64 ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt h1
  have h2le : old.toNat / 2 ^ 224 ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt h2
  have h1term : 2 ^ 160 * (val.toNat % 2 ^ 64) ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
    Nat.mul_le_mul_left _ h1le
  have h2term : 2 ^ 224 * (old.toNat / 2 ^ 224) ≤ 2 ^ 224 * (2 ^ 32 - 1) :=
    Nat.mul_le_mul_left _ h2le
  have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) +
      2 ^ 224 * (2 ^ 32 - 1) < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem setRewardConfigUInt64Mask_toNat_lt (v : UInt256) :
    (UInt256.land v uint64Mask).toNat < 2 ^ 64 := by
  rw [u256_land_toNat, uint64Mask_toNat]
  have hle : Nat.land v.toNat (2 ^ 64 - 1) ≤ 2 ^ 64 - 1 := nat_land_le_right _ _
  have hltSize : Nat.land v.toNat (2 ^ 64 - 1) < UInt256.size := by
    have hlt : Nat.land v.toNat (2 ^ 64 - 1) < 2 ^ 64 := by omega
    norm_num [UInt256.size] at hlt ⊢
    omega
  rw [Nat.mod_eq_of_lt hltSize]
  omega

theorem setRewardConfigShiftLeft160_uint64Mask_toNat (v : UInt256) :
    (UInt256.shiftLeft (UInt256.land v uint64Mask) ⟨160⟩).toNat =
      (UInt256.land v uint64Mask).toNat * 2 ^ 160 := by
  unfold UInt256.shiftLeft UInt256.toNat
  show (Fin.shiftLeft (UInt256.land v uint64Mask).val (⟨160⟩ : UInt256).val).val = _
  unfold Fin.shiftLeft
  rw [show (⟨160⟩ : UInt256).val = 160 by rfl]
  change ((UInt256.land v uint64Mask).toNat <<< 160) % UInt256.size =
    (UInt256.land v uint64Mask).toNat * 2 ^ 160
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  have hsmall := setRewardConfigUInt64Mask_toNat_lt v
  calc
    (UInt256.land v uint64Mask).val.val * 2 ^ 160 < 2 ^ 64 * 2 ^ 160 :=
      Nat.mul_lt_mul_of_pos_right hsmall (by norm_num)
    _ = 2 ^ 224 := by rw [← Nat.pow_add]
    _ < UInt256.size := by norm_num [UInt256.size]

set_option maxRecDepth 2000000 in
theorem setRewardConfigNatLandClearMiddle160_224 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 160 - 1 + ((2 : Nat) ^ 256 - 2 ^ 224)) =
      n % 2 ^ 160 + (n / 2 ^ 224) * 2 ^ 224 := by
  have hhighMask : (2 : Nat) ^ 256 - 2 ^ 224 = (2 ^ 32 - 1) * 2 ^ 224 := by
    norm_num [Nat.pow_add]
  have hmask :
      (2 : Nat) ^ 160 - 1 + ((2 : Nat) ^ 256 - 2 ^ 224) =
        Nat.lor (2 ^ 160 - 1) ((2 ^ 32 - 1) * 2 ^ 224) := by
    rw [hhighMask]
    rw [nat_lor_shift_add (2 ^ 160 - 1) (2 ^ 32 - 1) 224]
    norm_num
  have hrhs :
      n % 2 ^ 160 + (n / 2 ^ 224) * 2 ^ 224 =
        Nat.lor (n % 2 ^ 160) ((n / 2 ^ 224) * 2 ^ 224) := by
    rw [nat_lor_shift_add (n % 2 ^ 160) (n / 2 ^ 224) 224]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  rw [hmask, hrhs]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 160 - 1) ||| ((2 ^ 32 - 1) * 2 ^ 224))).testBit i =
    ((n % 2 ^ 160) ||| (n / 2 ^ 224 * 2 ^ 224)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi160 : i < 160
  · have hi224 : i < 224 := by omega
    simp [hi160, hi224]
  · by_cases hi224 : i < 224
    · have hnot224 : ¬ 224 ≤ i := by omega
      simp [hi160, hnot224]
    · have h224 : 224 ≤ i := Nat.le_of_not_gt hi224
      by_cases hi256 : i < 256
      · have hlow32 : i - 224 < 32 := by omega
        simp [hi160, h224]
        rw [show Nat.testBit 4294967295 (i - 224) = true by
          change Nat.testBit (2 ^ 32 - 1) (i - 224) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlow32]]
        simp
        change n.testBit i = (n / 2 ^ 224).testBit (i - 224)
        exact (divPow_testBit n 224 i h224).symm
      · have hnbit : n.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
            (Nat.pow_le_pow_right (by norm_num) (by omega : (256 : Nat) ≤ i)))
        have hq : n / 2 ^ 224 < 2 ^ 32 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
          exact hn
        have hqbit : (n / 2 ^ 224).testBit (i - 224) = false :=
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num)
              (by omega : (32 : Nat) ≤ i - 224)))
        simp [hi160, h224, hnbit]
        simpa [show
          26959946667150639794667015087019630673637144422540572481103610249216 =
            (2 : Nat) ^ 224 by norm_num] using hqbit

theorem setRewardConfigNatLandShiftLeft160_mid64 (n : Nat) :
    Nat.land ((n <<< 160) % 2 ^ 256) ((2 : Nat) ^ 224 - 2 ^ 160) =
      (n % 2 ^ 64) * 2 ^ 160 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (2 : Nat) ^ 224 - 2 ^ 160 = (2 ^ 64 - 1) * 2 ^ 160 by
    norm_num [Nat.pow_add]]
  change (((n <<< 160) % 2 ^ 256) &&& ((2 ^ 64 - 1) * 2 ^ 160)).testBit i =
    (n % 2 ^ 64 * 2 ^ 160).testBit i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow, testBit_shiftLeft]
  by_cases hi160 : i < 160
  · simp [hi160]
  · have h160 : 160 ≤ i := Nat.le_of_not_gt hi160
    by_cases hi224 : i < 224
    · have h64 : i - 160 < 64 := by omega
      have hi256 : i < 256 := by omega
      simp [hi160, h160, hi256, h64]
      rw [show Nat.testBit 18446744073709551615 (i - 160) = true by
        change Nat.testBit (2 ^ 64 - 1) (i - 160) = true
        rw [Nat.testBit_two_pow_sub_one]
        simp [h64]]
      simp
    · have hnot64 : ¬ i - 160 < 64 := by omega
      by_cases hi256 : i < 256
      · simp [hi160, h160, hi256, hnot64]
        rw [show Nat.testBit 18446744073709551615 (i - 160) = false by
          change Nat.testBit (2 ^ 64 - 1) (i - 160) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot64]]
        simp
      · simp [hi160, h160, hi256, hnot64]

theorem setRewardConfigNatLorPacked160_224 (low mid high : Nat)
    (hlow : low < 2 ^ 160) (hmid : mid < 2 ^ 64) :
    Nat.lor (low + high * 2 ^ 224) (mid * 2 ^ 160) =
      low + mid * 2 ^ 160 + high * 2 ^ 224 := by
  have hlow224 : low < 2 ^ 224 :=
    lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hclear : low + high * 2 ^ 224 = Nat.lor low (high * 2 ^ 224) := by
    rw [nat_lor_shift_add low high 224 hlow224]
  rw [hclear]
  rw [show Nat.lor (Nat.lor low (high * 2 ^ 224)) (mid * 2 ^ 160) =
      Nat.lor low (Nat.lor (mid * 2 ^ 160) (high * 2 ^ 224)) by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 224)) (mid * 2 ^ 160)
          = Nat.lor low (Nat.lor (high * 2 ^ 224) (mid * 2 ^ 160)) :=
            Nat.lor_assoc low (high * 2 ^ 224) (mid * 2 ^ 160)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 160) (high * 2 ^ 224)) := by
            rw [nat_lor_comm (high * 2 ^ 224) (mid * 2 ^ 160)]]
  rw [nat_lor_shift_add (mid * 2 ^ 160) high 224]
  · rw [show mid * 2 ^ 160 + high * 2 ^ 224 =
        (mid + high * 2 ^ 64) * 2 ^ 160 by ring]
    rw [nat_lor_shift_add low (mid + high * 2 ^ 64) 160 hlow]
    ring
  · calc
      mid * 2 ^ 160 < 2 ^ 64 * 2 ^ 160 :=
        Nat.mul_lt_mul_of_pos_right hmid (by norm_num)
      _ = 2 ^ 224 := by rw [← Nat.pow_add]

set_option maxRecDepth 2000000 in
theorem setRewardConfigUInt64Offset20Word_toNat (old val : UInt256) :
    (setRewardConfigUInt64Offset20Word old val).toNat =
      old.toNat % 2 ^ 160 + 2 ^ 160 * (val.toNat % 2 ^ 64) +
        2 ^ 224 * (old.toNat / 2 ^ 224) := by
  unfold setRewardConfigUInt64Offset20Word
  rw [u256_lor_toNat, u256_land_toNat, u256_land_toNat]
  have hclearMask :
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))).toNat =
        2 ^ 160 - 1 + ((2 : Nat) ^ 256 - 2 ^ 224) := by
    native_decide
  have hmidMask :
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).toNat =
        (2 : Nat) ^ 224 - 2 ^ 160 := by
    native_decide
  rw [hclearMask, hmidMask]
  have hshift :
      (UInt256.shiftLeft val ⟨160⟩).toNat = (val.toNat <<< 160) % 2 ^ 256 := by
    unfold UInt256.shiftLeft UInt256.toNat
    show (Fin.shiftLeft val.val (⟨160⟩ : UInt256).val).val = _
    unfold Fin.shiftLeft
    rw [show (⟨160⟩ : UInt256).val = 160 by rfl]
    change (val.toNat <<< 160) % UInt256.size = (val.toNat <<< 160) % 2 ^ 256
    norm_num [UInt256.size]
  rw [hshift]
  rw [setRewardConfigNatLandClearMiddle160_224 old.toNat (by
    change old.val.val < 2 ^ 256
    exact old.val.isLt)]
  rw [setRewardConfigNatLandShiftLeft160_mid64 val.toNat]
  have hclearLt :
      old.toNat % 2 ^ 160 + old.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hq : old.toNat / 2 ^ 224 < 2 ^ 32 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change old.val.val < 2 ^ 256
      exact old.val.isLt
    have hlowle : old.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 224 ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hq
    have hqterm : old.toNat / 2 ^ 224 * 2 ^ 224 ≤ (2 ^ 32 - 1) * 2 ^ 224 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 160 - 1) + (2 ^ 32 - 1) * 2 ^ 224 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hmidLt : (val.toNat % 2 ^ 64) * 2 ^ 160 < UInt256.size := by
    have h := Nat.mod_lt val.toNat (by norm_num : 0 < 2 ^ 64)
    calc
      (val.toNat % 2 ^ 64) * 2 ^ 160 < 2 ^ 64 * 2 ^ 160 :=
        Nat.mul_lt_mul_of_pos_right h (by norm_num)
      _ = 2 ^ 224 := by rw [← Nat.pow_add]
      _ < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hclearLt, Nat.mod_eq_of_lt hmidLt]
  have hlow : old.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
  have hmid : val.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hlor :
      Nat.lor
          (old.toNat % 2 ^ 160 + old.toNat / 2 ^ 224 * 2 ^ 224)
          (val.toNat % 2 ^ 64 * 2 ^ 160) =
        old.toNat % 2 ^ 160 + val.toNat % 2 ^ 64 * 2 ^ 160 +
          old.toNat / 2 ^ 224 * 2 ^ 224 :=
    setRewardConfigNatLorPacked160_224
      (old.toNat % 2 ^ 160) (val.toNat % 2 ^ 64)
      (old.toNat / 2 ^ 224) hlow hmid
  have hlorLt :
      Nat.lor
          (old.toNat % 2 ^ 160 + old.toNat / 2 ^ 224 * 2 ^ 224)
          (val.toNat % 2 ^ 64 * 2 ^ 160) < UInt256.size := by
    rw [hlor]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using setRewardConfigUInt64Offset20Nat_lt_size old val
  rw [Nat.mod_eq_of_lt hlorLt, hlor]
  ring

theorem setRewardConfigBoolOffset28Nat_lt_size (old bit : UInt256) :
    old.toNat % 2 ^ 224 + 2 ^ 224 * (bit.toNat % 2 ^ 8) +
      2 ^ 232 * (old.toNat / 2 ^ 232) < UInt256.size := by
  have h0 : old.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by norm_num)
  have h1 : bit.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  have h2 : old.toNat / 2 ^ 232 < 2 ^ 24 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have h0le : old.toNat % 2 ^ 224 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt h0
  have h1le : bit.toNat % 2 ^ 8 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt h1
  have h2le : old.toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt h2
  have h1term : 2 ^ 224 * (bit.toNat % 2 ^ 8) ≤ 2 ^ 224 * (2 ^ 8 - 1) :=
    Nat.mul_le_mul_left _ h1le
  have h2term : 2 ^ 232 * (old.toNat / 2 ^ 232) ≤ 2 ^ 232 * (2 ^ 24 - 1) :=
    Nat.mul_le_mul_left _ h2le
  have hmax : (2 ^ 224 - 1) + 2 ^ 224 * (2 ^ 8 - 1) +
      2 ^ 232 * (2 ^ 24 - 1) < UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  omega

theorem setRewardConfigUInt8Mask_toNat_lt (v : UInt256) :
    (UInt256.land v ⟨255⟩).toNat < 2 ^ 8 := by
  rw [u256_land_toNat]
  have hle : Nat.land v.toNat (⟨255⟩ : UInt256).toNat ≤ (⟨255⟩ : UInt256).toNat :=
    nat_land_le_right _ _
  have hmask : (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 := by native_decide
  rw [hmask] at hle ⊢
  have hltSize : Nat.land v.toNat (2 ^ 8 - 1) < UInt256.size := by
    have hlt : Nat.land v.toNat (2 ^ 8 - 1) < 2 ^ 8 := by omega
    norm_num [UInt256.size] at hlt ⊢
    omega
  rw [Nat.mod_eq_of_lt hltSize]
  omega

theorem setRewardConfigShiftLeft224_uint8Mask_toNat (v : UInt256) :
    (UInt256.shiftLeft (UInt256.land v ⟨255⟩) ⟨224⟩).toNat =
      (UInt256.land v ⟨255⟩).toNat * 2 ^ 224 := by
  unfold UInt256.shiftLeft UInt256.toNat
  show (Fin.shiftLeft (UInt256.land v ⟨255⟩).val (⟨224⟩ : UInt256).val).val = _
  unfold Fin.shiftLeft
  rw [show (⟨224⟩ : UInt256).val = 224 by rfl]
  change ((UInt256.land v ⟨255⟩).toNat <<< 224) % UInt256.size =
    (UInt256.land v ⟨255⟩).toNat * 2 ^ 224
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  have hsmall := setRewardConfigUInt8Mask_toNat_lt v
  calc
    (UInt256.land v ⟨255⟩).val.val * 2 ^ 224 < 2 ^ 8 * 2 ^ 224 :=
      Nat.mul_lt_mul_of_pos_right hsmall (by norm_num)
    _ = 2 ^ 232 := by rw [← Nat.pow_add]
    _ < UInt256.size := by norm_num [UInt256.size]

set_option maxRecDepth 2000000 in
theorem setRewardConfigNatLandClearMiddle224_232 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 224 - 1 + ((2 : Nat) ^ 256 - 2 ^ 232)) =
      n % 2 ^ 224 + (n / 2 ^ 232) * 2 ^ 232 := by
  have hhighMask : (2 : Nat) ^ 256 - 2 ^ 232 = (2 ^ 24 - 1) * 2 ^ 232 := by
    norm_num [Nat.pow_add]
  have hmask :
      (2 : Nat) ^ 224 - 1 + ((2 : Nat) ^ 256 - 2 ^ 232) =
        Nat.lor (2 ^ 224 - 1) ((2 ^ 24 - 1) * 2 ^ 232) := by
    rw [hhighMask]
    rw [nat_lor_shift_add (2 ^ 224 - 1) (2 ^ 24 - 1) 232]
    norm_num
  have hrhs :
      n % 2 ^ 224 + (n / 2 ^ 232) * 2 ^ 232 =
        Nat.lor (n % 2 ^ 224) ((n / 2 ^ 232) * 2 ^ 232) := by
    rw [nat_lor_shift_add (n % 2 ^ 224) (n / 2 ^ 232) 232]
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 224))
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  rw [hmask, hrhs]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 224 - 1) ||| ((2 ^ 24 - 1) * 2 ^ 232))).testBit i =
    ((n % 2 ^ 224) ||| (n / 2 ^ 232 * 2 ^ 232)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi224 : i < 224
  · have hi232 : i < 232 := by omega
    simp [hi224, hi232]
  · by_cases hi232 : i < 232
    · have hnot232 : ¬ 232 ≤ i := by omega
      simp [hi224, hnot232]
    · have h232 : 232 ≤ i := Nat.le_of_not_gt hi232
      by_cases hi256 : i < 256
      · have hlow24 : i - 232 < 24 := by omega
        simp [hi224, h232]
        rw [show Nat.testBit 16777215 (i - 232) = true by
          change Nat.testBit (2 ^ 24 - 1) (i - 232) = true
          rw [Nat.testBit_two_pow_sub_one]
          simp [hlow24]]
        simp
        change n.testBit i = (n / 2 ^ 232).testBit (i - 232)
        exact (divPow_testBit n 232 i h232).symm
      · have hnbit : n.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
            (Nat.pow_le_pow_right (by norm_num) (by omega : (256 : Nat) ≤ i)))
        have hq : n / 2 ^ 232 < 2 ^ 24 := by
          apply Nat.div_lt_of_lt_mul
          rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
          exact hn
        have hqbit : (n / 2 ^ 232).testBit (i - 232) = false :=
          Nat.testBit_lt_two_pow
            (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num)
              (by omega : (24 : Nat) ≤ i - 232)))
        simp [hi224, h232, hnbit]
        simpa [show
          6901746346790563787434755862277025452451108972170386555162524223799296 =
            (2 : Nat) ^ 232 by norm_num] using hqbit

theorem setRewardConfigNatLandShiftLeft224_mid8 (n : Nat) :
    Nat.land ((n <<< 224) % 2 ^ 256) (((2 : Nat) ^ 8 - 1) * 2 ^ 224) =
      (n % 2 ^ 8) * 2 ^ 224 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((n <<< 224) % 2 ^ 256) &&& ((2 ^ 8 - 1) * 2 ^ 224)).testBit i =
    (n % 2 ^ 8 * 2 ^ 224).testBit i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow, testBit_shiftLeft]
  by_cases hi224 : i < 224
  · simp [hi224]
  · have h224 : 224 ≤ i := Nat.le_of_not_gt hi224
    by_cases hi232 : i < 232
    · have h8 : i - 224 < 8 := by omega
      have hi256 : i < 256 := by omega
      simp [hi224, h224, hi256, h8]
      rw [show Nat.testBit 255 (i - 224) = true by
        change Nat.testBit (2 ^ 8 - 1) (i - 224) = true
        rw [Nat.testBit_two_pow_sub_one]
        simp [h8]]
      simp
    · have hnot8 : ¬ i - 224 < 8 := by omega
      by_cases hi256 : i < 256
      · simp [hi224, h224, hi256, hnot8]
        rw [show Nat.testBit 255 (i - 224) = false by
          change Nat.testBit (2 ^ 8 - 1) (i - 224) = false
          rw [Nat.testBit_two_pow_sub_one]
          simp [hnot8]]
        simp
      · simp [hi224, h224, hi256, hnot8]

theorem setRewardConfigNatLorPacked224_232 (low mid high : Nat)
    (hlow : low < 2 ^ 224) (hmid : mid < 2 ^ 8) :
    Nat.lor (low + high * 2 ^ 232) (mid * 2 ^ 224) =
      low + mid * 2 ^ 224 + high * 2 ^ 232 := by
  have hlow232 : low < 2 ^ 232 :=
    lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hclear : low + high * 2 ^ 232 = Nat.lor low (high * 2 ^ 232) := by
    rw [nat_lor_shift_add low high 232 hlow232]
  rw [hclear]
  rw [show Nat.lor (Nat.lor low (high * 2 ^ 232)) (mid * 2 ^ 224) =
      Nat.lor low (Nat.lor (mid * 2 ^ 224) (high * 2 ^ 232)) by
    calc
      Nat.lor (Nat.lor low (high * 2 ^ 232)) (mid * 2 ^ 224)
          = Nat.lor low (Nat.lor (high * 2 ^ 232) (mid * 2 ^ 224)) :=
            Nat.lor_assoc low (high * 2 ^ 232) (mid * 2 ^ 224)
      _ = Nat.lor low (Nat.lor (mid * 2 ^ 224) (high * 2 ^ 232)) := by
            rw [nat_lor_comm (high * 2 ^ 232) (mid * 2 ^ 224)]]
  rw [nat_lor_shift_add (mid * 2 ^ 224) high 232]
  · rw [show mid * 2 ^ 224 + high * 2 ^ 232 =
        (mid + high * 2 ^ 8) * 2 ^ 224 by ring]
    rw [nat_lor_shift_add low (mid + high * 2 ^ 8) 224 hlow]
    ring
  · calc
      mid * 2 ^ 224 < 2 ^ 8 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hmid (by norm_num)
      _ = 2 ^ 232 := by rw [← Nat.pow_add]

set_option maxRecDepth 2000000 in
theorem setRewardConfigBoolOffset28Word_toNat (old bit : UInt256) :
    (setRewardConfigBoolOffset28Word old bit).toNat =
      old.toNat % 2 ^ 224 + 2 ^ 224 * (bit.toNat % 2 ^ 8) +
        2 ^ 232 * (old.toNat / 2 ^ 232) := by
  unfold setRewardConfigBoolOffset28Word
  rw [u256_lor_toNat, u256_land_toNat, u256_land_toNat]
  have hclearMask :
      (UInt256.lnot (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)).toNat =
        2 ^ 224 - 1 + ((2 : Nat) ^ 256 - 2 ^ 232) := by
    native_decide
  have hmidMask :
      (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).toNat =
        ((2 : Nat) ^ 8 - 1) * 2 ^ 224 := by
    native_decide
  rw [hclearMask, hmidMask]
  have hshift :
      (UInt256.shiftLeft bit ⟨224⟩).toNat = (bit.toNat <<< 224) % 2 ^ 256 := by
    unfold UInt256.shiftLeft UInt256.toNat
    show (Fin.shiftLeft bit.val (⟨224⟩ : UInt256).val).val = _
    unfold Fin.shiftLeft
    rw [show (⟨224⟩ : UInt256).val = 224 by rfl]
    change (bit.toNat <<< 224) % UInt256.size = (bit.toNat <<< 224) % 2 ^ 256
    norm_num [UInt256.size]
  rw [hshift]
  rw [setRewardConfigNatLandClearMiddle224_232 old.toNat (by
    change old.val.val < 2 ^ 256
    exact old.val.isLt)]
  rw [setRewardConfigNatLandShiftLeft224_mid8 bit.toNat]
  have hclearLt :
      old.toNat % 2 ^ 224 + old.toNat / 2 ^ 232 * 2 ^ 232 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by norm_num)
    have hq : old.toNat / 2 ^ 232 < 2 ^ 24 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 232 * 2 ^ 24 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change old.val.val < 2 ^ 256
      exact old.val.isLt
    have hlowle : old.toNat % 2 ^ 224 ≤ 2 ^ 224 - 1 := Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 232 ≤ 2 ^ 24 - 1 := Nat.le_pred_of_lt hq
    have hqterm : old.toNat / 2 ^ 232 * 2 ^ 232 ≤ (2 ^ 24 - 1) * 2 ^ 232 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 224 - 1) + (2 ^ 24 - 1) * 2 ^ 232 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  have hmidLt : (bit.toNat % 2 ^ 8) * 2 ^ 224 < UInt256.size := by
    have h := Nat.mod_lt bit.toNat (by norm_num : 0 < 2 ^ 8)
    calc
      (bit.toNat % 2 ^ 8) * 2 ^ 224 < 2 ^ 8 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right h (by norm_num)
      _ = 2 ^ 232 := by rw [← Nat.pow_add]
      _ < UInt256.size := by norm_num [UInt256.size]
  rw [Nat.mod_eq_of_lt hclearLt, Nat.mod_eq_of_lt hmidLt]
  have hlow : old.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by norm_num)
  have hmid : bit.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  have hlor :
      Nat.lor
          (old.toNat % 2 ^ 224 + old.toNat / 2 ^ 232 * 2 ^ 232)
          (bit.toNat % 2 ^ 8 * 2 ^ 224) =
        old.toNat % 2 ^ 224 + bit.toNat % 2 ^ 8 * 2 ^ 224 +
          old.toNat / 2 ^ 232 * 2 ^ 232 :=
    setRewardConfigNatLorPacked224_232
      (old.toNat % 2 ^ 224) (bit.toNat % 2 ^ 8)
      (old.toNat / 2 ^ 232) hlow hmid
  have hlorLt :
      Nat.lor
          (old.toNat % 2 ^ 224 + old.toNat / 2 ^ 232 * 2 ^ 232)
          (bit.toNat % 2 ^ 8 * 2 ^ 224) < UInt256.size := by
    rw [hlor]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using setRewardConfigBoolOffset28Nat_lt_size old bit
  rw [Nat.mod_eq_of_lt hlorLt, hlor]
  ring

def setRewardConfigSlot0AfterToken (old token : UInt256) : UInt256 :=
  setAddressOffset0Word old token

theorem setRewardConfigAddressOffset0Word_toNat_masked (old addr : UInt256) :
    (setAddressOffset0Word old addr).toNat =
      addr.toNat % 2 ^ 160 + old.toNat / 2 ^ 160 * 2 ^ 160 := by
  unfold setAddressOffset0Word
  rw [u256_lor_toNat, addressOffset0High160Mask_toNat, u256_land_toNat]
  have hmask : solcAddrMask.toNat = 2 ^ 160 - 1 := by
    native_decide
  rw [hmask, nat_land_mask_eq_mod]
  have haddrLt : addr.toNat % 2 ^ 160 < UInt256.size := by
    have h := Nat.mod_lt addr.toNat (by norm_num : 0 < 2 ^ 160)
    norm_num [UInt256.size] at h ⊢
    omega
  rw [Nat.mod_eq_of_lt haddrLt]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add (addr.toNat % 2 ^ 160) (old.toNat / 2 ^ 160) 160
    (Nat.mod_lt _ (by norm_num))]
  have hsumLt :
      addr.toNat % 2 ^ 160 + old.toNat / 2 ^ 160 * 2 ^ 160 < UInt256.size := by
    have hlow : addr.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt _ (by norm_num)
    have hq : old.toNat / 2 ^ 160 < 2 ^ 96 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 160 * 2 ^ 96 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      change old.val.val < 2 ^ 256
      exact old.val.isLt
    have hlowle : addr.toNat % 2 ^ 160 ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hqle : old.toNat / 2 ^ 160 ≤ 2 ^ 96 - 1 := Nat.le_pred_of_lt hq
    have hqterm :
        old.toNat / 2 ^ 160 * 2 ^ 160 ≤ (2 ^ 96 - 1) * 2 ^ 160 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 160 - 1) + (2 ^ 96 - 1) * 2 ^ 160 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]

def setRewardConfigSlot0AfterRescale (old token rescale : UInt256) : UInt256 :=
  setRewardConfigUInt64Offset20Word (setRewardConfigSlot0AfterToken old token) rescale

def setRewardConfigSlot0Final (old token rescale bit : UInt256) : UInt256 :=
  setRewardConfigBoolOffset28Word (setRewardConfigSlot0AfterRescale old token rescale) bit

abbrev setRewardConfigSlot0Down (old token rescale : UInt256) : UInt256 :=
  setRewardConfigSlot0Final old token rescale ⟨0⟩

abbrev setRewardConfigSlot0Up (old token rescale : UInt256) : UInt256 :=
  setRewardConfigSlot0Final old token rescale ⟨1⟩

set_option maxHeartbeats 1000000 in
theorem setRewardConfigSlot0Down_toNat (old token rescale : UInt256) :
    (setRewardConfigSlot0Down old token rescale).toNat =
      token.toNat % 2 ^ 160 + 2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 232 * (old.toNat / 2 ^ 232) := by
  unfold setRewardConfigSlot0Down setRewardConfigSlot0Final
    setRewardConfigSlot0AfterRescale setRewardConfigSlot0AfterToken
  rw [setRewardConfigBoolOffset28Word_toNat, setRewardConfigUInt64Offset20Word_toNat]
  rw [show (⟨0⟩ : UInt256).toNat % 2 ^ 8 = 0 by rfl]
  simp only [mul_zero, add_zero]
  have haddrNat := setRewardConfigAddressOffset0Word_toNat_masked old token
  let low : Nat := token.toNat % 2 ^ 160
  let mid : Nat := rescale.toNat % 2 ^ 64
  let q160 : Nat := old.toNat / 2 ^ 160
  let q224 : Nat := old.toNat / 2 ^ 224
  have hlow : low < 2 ^ 160 := by
    exact Nat.mod_lt _ (by norm_num)
  have hmid : mid < 2 ^ 64 := by
    exact Nat.mod_lt _ (by norm_num)
  have hlow224 : low + 2 ^ 160 * mid < 2 ^ 224 := by
    have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hmidle : mid ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt hmid
    have hmidterm : 2 ^ 160 * mid ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ hmidle
    have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) < 2 ^ 224 := by
      norm_num [Nat.pow_add]
    omega
  have haddr_mod160 :
      (setAddressOffset0Word old token).toNat % 2 ^ 160 = low := by
    rw [haddrNat]
    change (low + q160 * 2 ^ 160) % 2 ^ 160 = low
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow]
  have haddr_div160 :
      (low + q160 * 2 ^ 160) / 2 ^ 160 = q160 := by
    rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 160)]
    rw [Nat.div_eq_of_lt hlow]
    simp
  have haddr_div224 :
      (setAddressOffset0Word old token).toNat / 2 ^ 224 = q224 := by
    rw [haddrNat]
    change (low + q160 * 2 ^ 160) / 2 ^ 224 = q224
    rw [show (2 : Nat) ^ 224 = 2 ^ 160 * 2 ^ 64 by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [haddr_div160]
    change old.toNat / 2 ^ 160 / 2 ^ 64 = old.toNat / 2 ^ 224
    rw [Nat.div_div_eq_div_mul]
    rw [show (2 : Nat) ^ 160 * 2 ^ 64 = 2 ^ 224 by rw [← Nat.pow_add]]
  have hslot1_mod224 :
      ((setAddressOffset0Word old token).toNat % 2 ^ 160 +
          2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 * ((setAddressOffset0Word old token).toNat / 2 ^ 224)) %
          2 ^ 224 =
        low + 2 ^ 160 * mid := by
    rw [haddr_mod160, haddr_div224]
    change (low + 2 ^ 160 * mid + 2 ^ 224 * q224) % 2 ^ 224 =
      low + 2 ^ 160 * mid
    rw [show low + 2 ^ 160 * mid + 2 ^ 224 * q224 =
        low + 2 ^ 160 * mid + q224 * 2 ^ 224 by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlow224
  have hslot1_div224 :
      (low + 2 ^ 160 * mid + q224 * 2 ^ 224) / 2 ^ 224 = q224 := by
    rw [show low + 2 ^ 160 * mid + q224 * 2 ^ 224 =
        (low + 2 ^ 160 * mid) + q224 * 2 ^ 224 by ring]
    rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 224)]
    rw [Nat.div_eq_of_lt hlow224]
    simp
  have hslot1_div232 :
      ((setAddressOffset0Word old token).toNat % 2 ^ 160 +
          2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 * ((setAddressOffset0Word old token).toNat / 2 ^ 224)) /
          2 ^ 232 =
        old.toNat / 2 ^ 232 := by
    rw [haddr_mod160, haddr_div224]
    change (low + 2 ^ 160 * mid + 2 ^ 224 * q224) / 2 ^ 232 =
      old.toNat / 2 ^ 232
    rw [show low + 2 ^ 160 * mid + 2 ^ 224 * q224 =
        low + 2 ^ 160 * mid + q224 * 2 ^ 224 by ring]
    rw [show (2 : Nat) ^ 232 = 2 ^ 224 * 2 ^ 8 by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [hslot1_div224]
    change old.toNat / 2 ^ 224 / 2 ^ 8 = old.toNat / 2 ^ 232
    rw [Nat.div_div_eq_div_mul]
    rw [show (2 : Nat) ^ 224 * 2 ^ 8 = 2 ^ 232 by rw [← Nat.pow_add]]
  rw [hslot1_mod224, hslot1_div232]

set_option maxHeartbeats 1000000 in
theorem setRewardConfigSlot0Up_toNat (old token rescale : UInt256) :
    (setRewardConfigSlot0Up old token rescale).toNat =
      token.toNat % 2 ^ 160 + 2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 + 2 ^ 232 * (old.toNat / 2 ^ 232) := by
  unfold setRewardConfigSlot0Up setRewardConfigSlot0Final
    setRewardConfigSlot0AfterRescale setRewardConfigSlot0AfterToken
  rw [setRewardConfigBoolOffset28Word_toNat, setRewardConfigUInt64Offset20Word_toNat]
  rw [show (⟨1⟩ : UInt256).toNat % 2 ^ 8 = 1 by rfl]
  have haddrNat := setRewardConfigAddressOffset0Word_toNat_masked old token
  let low : Nat := token.toNat % 2 ^ 160
  let mid : Nat := rescale.toNat % 2 ^ 64
  let q160 : Nat := old.toNat / 2 ^ 160
  let q224 : Nat := old.toNat / 2 ^ 224
  have hlow : low < 2 ^ 160 := by
    exact Nat.mod_lt _ (by norm_num)
  have hmid : mid < 2 ^ 64 := by
    exact Nat.mod_lt _ (by norm_num)
  have hlow224 : low + 2 ^ 160 * mid < 2 ^ 224 := by
    have hlowle : low ≤ 2 ^ 160 - 1 := Nat.le_pred_of_lt hlow
    have hmidle : mid ≤ 2 ^ 64 - 1 := Nat.le_pred_of_lt hmid
    have hmidterm : 2 ^ 160 * mid ≤ 2 ^ 160 * (2 ^ 64 - 1) :=
      Nat.mul_le_mul_left _ hmidle
    have hmax : (2 ^ 160 - 1) + 2 ^ 160 * (2 ^ 64 - 1) < 2 ^ 224 := by
      norm_num [Nat.pow_add]
    omega
  have haddr_mod160 :
      (setAddressOffset0Word old token).toNat % 2 ^ 160 = low := by
    rw [haddrNat]
    change (low + q160 * 2 ^ 160) % 2 ^ 160 = low
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow]
  have haddr_div160 :
      (low + q160 * 2 ^ 160) / 2 ^ 160 = q160 := by
    rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 160)]
    rw [Nat.div_eq_of_lt hlow]
    simp
  have haddr_div224 :
      (setAddressOffset0Word old token).toNat / 2 ^ 224 = q224 := by
    rw [haddrNat]
    change (low + q160 * 2 ^ 160) / 2 ^ 224 = q224
    rw [show (2 : Nat) ^ 224 = 2 ^ 160 * 2 ^ 64 by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [haddr_div160]
    change old.toNat / 2 ^ 160 / 2 ^ 64 = old.toNat / 2 ^ 224
    rw [Nat.div_div_eq_div_mul]
    rw [show (2 : Nat) ^ 160 * 2 ^ 64 = 2 ^ 224 by rw [← Nat.pow_add]]
  have hslot1_mod224 :
      ((setAddressOffset0Word old token).toNat % 2 ^ 160 +
          2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 * ((setAddressOffset0Word old token).toNat / 2 ^ 224)) %
          2 ^ 224 =
        low + 2 ^ 160 * mid := by
    rw [haddr_mod160, haddr_div224]
    change (low + 2 ^ 160 * mid + 2 ^ 224 * q224) % 2 ^ 224 =
      low + 2 ^ 160 * mid
    rw [show low + 2 ^ 160 * mid + 2 ^ 224 * q224 =
        low + 2 ^ 160 * mid + q224 * 2 ^ 224 by ring]
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlow224
  have hslot1_div224 :
      (low + 2 ^ 160 * mid + q224 * 2 ^ 224) / 2 ^ 224 = q224 := by
    rw [show low + 2 ^ 160 * mid + q224 * 2 ^ 224 =
        (low + 2 ^ 160 * mid) + q224 * 2 ^ 224 by ring]
    rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 224)]
    rw [Nat.div_eq_of_lt hlow224]
    simp
  have hslot1_div232 :
      ((setAddressOffset0Word old token).toNat % 2 ^ 160 +
          2 ^ 160 * (rescale.toNat % 2 ^ 64) +
        2 ^ 224 * ((setAddressOffset0Word old token).toNat / 2 ^ 224)) /
          2 ^ 232 =
        old.toNat / 2 ^ 232 := by
    rw [haddr_mod160, haddr_div224]
    change (low + 2 ^ 160 * mid + 2 ^ 224 * q224) / 2 ^ 232 =
      old.toNat / 2 ^ 232
    rw [show low + 2 ^ 160 * mid + 2 ^ 224 * q224 =
        low + 2 ^ 160 * mid + q224 * 2 ^ 224 by ring]
    rw [show (2 : Nat) ^ 232 = 2 ^ 224 * 2 ^ 8 by rw [← Nat.pow_add]]
    rw [← Nat.div_div_eq_div_mul]
    rw [hslot1_div224]
    change old.toNat / 2 ^ 224 / 2 ^ 8 = old.toNat / 2 ^ 232
    rw [Nat.div_div_eq_div_mul]
    rw [show (2 : Nat) ^ 224 * 2 ^ 8 = 2 ^ 232 by rw [← Nat.pow_add]]
  rw [hslot1_mod224, hslot1_div232]
  ring

set_option maxHeartbeats 1000000 in
private theorem setRewardConfigSlot0Down_bytecodeExpr_toNat
    (old token rescale : UInt256) :
    (((UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)).lor
        ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩))))))).toNat =
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
  have hpackedLt : low + 2 ^ 160 * mid + 2 ^ 232 * high < UInt256.size := by
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
      (UInt256.land solcAddrMask token).toNat = low := by
    rw [u256_land_comm solcAddrMask token, u256_land_toNat]
    have hmask : solcAddrMask.toNat = 2 ^ 160 - 1 := by
      native_decide
    rw [hmask, nat_land_mask_eq_mod]
    have hlt : token.toNat % 2 ^ 160 < UInt256.size := by
      have h := Nat.mod_lt token.toNat (by norm_num : 0 < 2 ^ 160)
      norm_num [UInt256.size] at h ⊢
      omega
    rw [Nat.mod_eq_of_lt hlt]
  have hOldHigh :
      (UInt256.land old
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
          ⟨1⟩))).toNat = high * 2 ^ 232 := by
    rw [u256_land_toNat]
    have hmask :
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
          ⟨1⟩)).toNat = 2 ^ 256 - 2 ^ 232 := by
      native_decide
    rw [hmask]
    rw [natLandClearLow old.toNat 232 (by norm_num) (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)]
    have hlt : old.toNat / 2 ^ 232 * 2 ^ 232 < UInt256.size :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
    rw [Nat.mod_eq_of_lt hlt]
  have hlowHigh :
      ((UInt256.land solcAddrMask token).lor
        (UInt256.land old
          (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
            ⟨1⟩)))).toNat =
        low + high * 2 ^ 232 := by
    rw [u256_lor_toNat, htokenLow, hOldHigh]
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
      ((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
            (UInt256.shiftLeft rescale ⟨160⟩)).toNat =
        mid * 2 ^ 160 := by
    rw [u256_land_comm, u256_land_toNat]
    have hmask :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).toNat =
          (2 : Nat) ^ 224 - 2 ^ 160 := by
      native_decide
    have hshift :
        (UInt256.shiftLeft rescale ⟨160⟩).toNat =
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
  have hpacked :
      ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩)))))).toNat =
        low + 2 ^ 160 * mid + 2 ^ 232 * high := by
    rw [u256_lor_toNat, hmidWord, hlowHigh]
    rw [nat_lor_comm]
    have hlor :
        Nat.lor (low + high * 2 ^ 232) (mid * 2 ^ 160) =
          low + mid * 2 ^ 160 + high * 2 ^ 232 := by
      rw [show high * 2 ^ 232 = (high * 2 ^ 8) * 2 ^ 224 by ring]
      exact setRewardConfigNatLorPacked160_224 low mid (high * 2 ^ 8) hlow hmid
    rw [hlor]
    rw [show low + mid * 2 ^ 160 + high * 2 ^ 232 =
        low + 2 ^ 160 * mid + 2 ^ 232 * high by ring]
    exact Nat.mod_eq_of_lt hpackedLt
  have hprefix :
      (UInt256.land (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)) =
        (⟨0⟩ : UInt256) := by
    native_decide
  rw [hprefix]
  rw [show UInt256.lor (⟨0⟩ : UInt256)
      ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩)))))) =
        ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩)))))) by
      rw [u256_lor_comm]
      exact u256_lor_zero _]
  rw [hpacked]

private theorem setRewardConfigSlot0Down_bytecodeExpr
    (old token rescale : UInt256) :
    ((UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)).lor
      ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
            (UInt256.shiftLeft rescale ⟨160⟩)).lor
        ((UInt256.land solcAddrMask token).lor
          (UInt256.land old
            (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
              ⟨1⟩)))))) =
      setRewardConfigSlot0Down old token rescale := by
  apply u256_inj
  rw [setRewardConfigSlot0Down_bytecodeExpr_toNat, setRewardConfigSlot0Down_toNat]

set_option maxHeartbeats 1000000 in
private theorem setRewardConfigSlot0Up_bytecodeExpr_toNat
    (old token rescale : UInt256) :
    (((UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)).lor
        ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩))))))).toNat =
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
  have htokenLow :
      (UInt256.land solcAddrMask token).toNat = low := by
    rw [u256_land_comm solcAddrMask token, u256_land_toNat]
    have hmask : solcAddrMask.toNat = 2 ^ 160 - 1 := by
      native_decide
    rw [hmask, nat_land_mask_eq_mod]
    have hlt : token.toNat % 2 ^ 160 < UInt256.size := by
      have h := Nat.mod_lt token.toNat (by norm_num : 0 < 2 ^ 160)
      norm_num [UInt256.size] at h ⊢
      omega
    rw [Nat.mod_eq_of_lt hlt]
  have hOldHigh :
      (UInt256.land old
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
          ⟨1⟩))).toNat = high * 2 ^ 232 := by
    rw [u256_land_toNat]
    have hmask :
        (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
          ⟨1⟩)).toNat = 2 ^ 256 - 2 ^ 232 := by
      native_decide
    rw [hmask]
    rw [natLandClearLow old.toNat 232 (by norm_num) (by
      change old.val.val < 2 ^ 256
      exact old.val.isLt)]
    have hlt : old.toNat / 2 ^ 232 * 2 ^ 232 < UInt256.size :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
    rw [Nat.mod_eq_of_lt hlt]
  have hlowHigh :
      ((UInt256.land solcAddrMask token).lor
        (UInt256.land old
          (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
            ⟨1⟩)))).toNat =
        low + high * 2 ^ 232 := by
    rw [u256_lor_toNat, htokenLow, hOldHigh]
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
      ((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
            (UInt256.shiftLeft rescale ⟨160⟩)).toNat =
        mid * 2 ^ 160 := by
    rw [u256_land_comm, u256_land_toNat]
    have hmask :
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).toNat =
          (2 : Nat) ^ 224 - 2 ^ 160 := by
      native_decide
    have hshift :
        (UInt256.shiftLeft rescale ⟨160⟩).toNat =
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
  have hpacked :
      ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask token).lor
            (UInt256.land old
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩)))))).toNat =
        low + 2 ^ 160 * mid + 2 ^ 232 * high := by
    rw [u256_lor_toNat, hmidWord, hlowHigh]
    rw [nat_lor_comm]
    have hlor :
        Nat.lor (low + high * 2 ^ 232) (mid * 2 ^ 160) =
          low + mid * 2 ^ 160 + high * 2 ^ 232 := by
      rw [show high * 2 ^ 232 = (high * 2 ^ 8) * 2 ^ 224 by ring]
      exact setRewardConfigNatLorPacked160_224 low mid (high * 2 ^ 8) hlow hmid
    rw [hlor]
    rw [show low + mid * 2 ^ 160 + high * 2 ^ 232 =
        low + 2 ^ 160 * mid + 2 ^ 232 * high by ring]
    exact Nat.mod_eq_of_lt hpackedLt
  have hprefix :
      (UInt256.land (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)) =
        UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩ := by
    native_decide
  rw [hprefix]
  rw [u256_lor_toNat, hpacked]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩).toNat = 2 ^ 224 by
    native_decide]
  rw [nat_lor_comm]
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

private theorem setRewardConfigSlot0Up_bytecodeExpr
    (old token rescale : UInt256) :
    ((UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).land
        (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)).lor
      ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
            (UInt256.shiftLeft rescale ⟨160⟩)).lor
        ((UInt256.land solcAddrMask token).lor
          (UInt256.land old
            (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
              ⟨1⟩)))))) =
      setRewardConfigSlot0Up old token rescale := by
  apply u256_inj
  rw [setRewardConfigSlot0Up_bytecodeExpr_toNat, setRewardConfigSlot0Up_toNat]

set_option maxHeartbeats 1000000 in
private theorem setRewardConfigSlot0Up_bytecodeExpr_runtime_toNat
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
  have htokenLow :
      (token.land solcAddrMask).toNat = low := by
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
  have hpacked :
      (((((⟨0xffffff⟩ : UInt256).shiftLeft ⟨232⟩).land old).lor
            (token.land solcAddrMask)).lor
          ((rescale.shiftLeft ⟨160⟩).land
            (((⟨1⟩ : UInt256).shiftLeft ⟨224⟩).sub
              ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩)))).toNat =
        low + 2 ^ 160 * mid + 2 ^ 232 * high := by
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
  have hprefix :
      ((((⟨1⟩ : UInt256).isZero.isZero).shiftLeft ⟨224⟩).land
        ((⟨255⟩ : UInt256).shiftLeft ⟨224⟩)).toNat = 2 ^ 224 := by
    native_decide
  rw [u256_lor_toNat, hpacked, hprefix]
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

private theorem setRewardConfigSlot0Up_bytecodeExpr_runtime
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
  rw [setRewardConfigSlot0Up_bytecodeExpr_runtime_toNat, setRewardConfigSlot0Up_toNat]

set_option maxHeartbeats 1000000 in
theorem setRewardConfigStorageLocStore_uint64_offset20 (evm : EVM.State)
    (slot val : UInt256) :
    storageLocStore evm (fieldLoc slot 20 8 (by decide) (.int uint64Int))
      (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setRewardConfigUInt64Offset20Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord fieldLoc loc
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20 ++
        (EVM.Word.toBytesLEWithSizeProof val).1.take 8 ++
        (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 28) =
      (setRewardConfigUInt64Offset20Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE_land_mask
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 20 (by decide)]
  rw [fromBytes'_take_wordLE_land_mask val 8 (by decide)]
  rw [fromBytes'_drop_wordLE
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 28]
  have hlen20 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 20).length = 20 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlen8 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 8).length = 8 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof val).2]
    norm_num
  rw [List.length_append, hlen20, hlen8]
  norm_num [Nat.pow_add]
  rw [setRewardConfigUInt64Offset20Word_toNat]
  rw [u256_land_toNat]
  rw [show (UInt256.ofNat 1461501637330902918203684832716283019655932542975 :
      UInt256).toNat = 2 ^ 160 - 1 by native_decide, nat_land_mask_eq_mod]
  have hlowLt :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat % 2 ^ 160 <
        UInt256.size := by
    have h := Nat.mod_lt (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
      (by norm_num : 0 < 2 ^ 160)
    norm_num [UInt256.size] at h ⊢
    omega
  rw [Nat.mod_eq_of_lt hlowLt]
  rw [u256_land_toNat]
  rw [show (UInt256.ofNat 18446744073709551615 : UInt256).toNat = 2 ^ 64 - 1 by
    native_decide, nat_land_mask_eq_mod]
  have hvalLt : val.toNat % 2 ^ 64 < UInt256.size := by
    have h := Nat.mod_lt val.toNat (by norm_num : 0 < 2 ^ 64)
    norm_num [UInt256.size] at h ⊢
    omega
  rw [Nat.mod_eq_of_lt hvalLt]
  ring

set_option maxHeartbeats 1000000 in
theorem setRewardConfigStorageLocStore_bool_false_offset28 (evm : EVM.State)
    (slot : UInt256) :
    storageLocStore evm (fieldLoc slot 28 1 (by decide) .bool) (.bool false) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setRewardConfigBoolOffset28Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) := by
  unfold storageLocStore storageLocWriteWord fieldLoc loc
  simp only [valueToWord, Bool.toUInt256_false, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 28 ++
        (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 1 ++
        (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 29) =
      (setRewardConfigBoolOffset28Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 28]
  rw [fromBytes'_take_wordLE (⟨0⟩ : UInt256) 1]
  rw [fromBytes'_drop_wordLE
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 29]
  have hlen28 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 28).length = 28 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 1).length = 1 := by
    native_decide
  rw [List.length_append, hlen28, hlen1]
  norm_num [Nat.pow_add]
  rw [setRewardConfigBoolOffset28Word_toNat]
  norm_num

set_option maxHeartbeats 1000000 in
theorem setRewardConfigStorageLocStore_bool_true_offset28 (evm : EVM.State)
    (slot : UInt256) :
    storageLocStore evm (fieldLoc slot 28 1 (by decide) .bool) (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setRewardConfigBoolOffset28Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord fieldLoc loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind, pure]
  congr 2
  apply u256_inj
  change fromBytes'
      ((EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 28 ++
        (EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).1.take 1 ++
        (EVM.Word.toBytesLEWithSizeProof
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop 29) =
      (setRewardConfigBoolOffset28Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨1⟩).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 28]
  rw [fromBytes'_take_wordLE (⟨1⟩ : UInt256) 1]
  rw [fromBytes'_drop_wordLE
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 29]
  have hlen28 :
      ((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 28).length = 28 := by
    rw [List.length_take,
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2]
    norm_num
  have hlen1 : ((EVM.Word.toBytesLEWithSizeProof (⟨1⟩ : UInt256)).1.take 1).length = 1 := by
    native_decide
  rw [List.length_append, hlen28, hlen1]
  norm_num [Nat.pow_add]
  rw [setRewardConfigBoolOffset28Word_toNat]
  norm_num

def setRewardConfigSourceAfterToken (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (setRewardConfigWithMultiplierSlotOf I)
    (setRewardConfigSlot0AfterToken
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (setRewardConfigWithMultiplierSlotOf I))
      (setRewardConfigWithMultiplierTokenWord I))

def setRewardConfigSourceAfterRescale (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) : EVM.State :=
  Solm.EVM.storageStore (setRewardConfigSourceAfterToken evm I)
    (setRewardConfigSourceAfterToken evm I).executionEnv.codeOwner
    (setRewardConfigWithMultiplierSlotOf I)
    (setRewardConfigUInt64Offset20Word
      (Solm.EVM.storageLoad (setRewardConfigSourceAfterToken evm I)
        (setRewardConfigSourceAfterToken evm I).executionEnv.codeOwner
        (setRewardConfigWithMultiplierSlotOf I))
      rescale)

def setRewardConfigSourceAfterShouldUpscale (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) (shouldUpscale : Bool) : EVM.State :=
  let evmRescale := setRewardConfigSourceAfterRescale evm I rescale
  Solm.EVM.storageStore evmRescale evmRescale.executionEnv.codeOwner
    (setRewardConfigWithMultiplierSlotOf I)
    (setRewardConfigBoolOffset28Word
      (Solm.EVM.storageLoad evmRescale evmRescale.executionEnv.codeOwner
        (setRewardConfigWithMultiplierSlotOf I))
      (if shouldUpscale then ⟨1⟩ else ⟨0⟩))

def setRewardConfigSourceFinal (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) (shouldUpscale : Bool) : EVM.State :=
  let evmBool := setRewardConfigSourceAfterShouldUpscale evm I rescale shouldUpscale
  Solm.EVM.storageStore evmBool evmBool.executionEnv.codeOwner
    (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
    (setRewardConfigWithMultiplierMultiplierWord I)

theorem setRewardConfigSourceFinal_false (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) :
    setRewardConfigSourceFinal evm I rescale false =
      Solm.EVM.storageStore (setRewardConfigSourceAfterShouldUpscale evm I rescale false)
        (setRewardConfigSourceAfterShouldUpscale evm I rescale false).executionEnv.codeOwner
        (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
        (setRewardConfigWithMultiplierMultiplierWord I) := by
  rfl

theorem setRewardConfigSourceFinal_true (evm : EVM.State) (I : ExecutionEnv)
    (rescale : UInt256) :
    setRewardConfigSourceFinal evm I rescale true =
      Solm.EVM.storageStore (setRewardConfigSourceAfterShouldUpscale evm I rescale true)
        (setRewardConfigSourceAfterShouldUpscale evm I rescale true).executionEnv.codeOwner
        (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
        (setRewardConfigWithMultiplierMultiplierWord I) := by
  rfl

set_option maxHeartbeats 5000000 in
theorem setRewardConfigSourceFinal_accountMap_equiv
    (evm : EVM.State) (I : ExecutionEnv) (rescale : UInt256) (shouldUpscale : Bool) :
    accountMapEquiv
      (sstoreAccountMap evm.executionEnv.codeOwner
        (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
          (setRewardConfigWithMultiplierSlotOf I)
          (setRewardConfigSlot0Final
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (setRewardConfigWithMultiplierSlotOf I))
            (setRewardConfigWithMultiplierTokenWord I) rescale
            (if shouldUpscale then ⟨1⟩ else ⟨0⟩)))
        (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
        (setRewardConfigWithMultiplierMultiplierWord I))
      (setRewardConfigSourceFinal evm I rescale shouldUpscale).accountMap := by
  let owner := evm.executionEnv.codeOwner
  let slot := setRewardConfigWithMultiplierSlotOf I
  let bit : UInt256 := if shouldUpscale then ⟨1⟩ else ⟨0⟩
  let old := Solm.EVM.storageLoad evm owner slot
  let tokenWord := setRewardConfigSlot0AfterToken old (setRewardConfigWithMultiplierTokenWord I)
  let rescaleWord := setRewardConfigSlot0AfterRescale old
    (setRewardConfigWithMultiplierTokenWord I) rescale
  let finalWord := setRewardConfigSlot0Final old
    (setRewardConfigWithMultiplierTokenWord I) rescale bit
  cases hacc : evm.accountMap.find? owner with
  | none =>
      have htoken : setRewardConfigSourceAfterToken evm I = evm := by
        unfold setRewardConfigSourceAfterToken
        simpa [owner, slot] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigSlot0AfterToken old (setRewardConfigWithMultiplierTokenWord I))
      have hrescale : setRewardConfigSourceAfterRescale evm I rescale = evm := by
        unfold setRewardConfigSourceAfterRescale
        rw [htoken]
        simpa [owner, slot] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigUInt64Offset20Word old rescale)
      have hbool : setRewardConfigSourceAfterShouldUpscale evm I rescale shouldUpscale = evm := by
        unfold setRewardConfigSourceAfterShouldUpscale
        rw [hrescale]
        simpa [owner, slot, bit] using
          storageStore_absent evm owner hacc slot
            (setRewardConfigBoolOffset28Word old bit)
      have hsource : setRewardConfigSourceFinal evm I rescale shouldUpscale = evm := by
        unfold setRewardConfigSourceFinal
        rw [hbool]
        simpa [owner, slot] using
          storageStore_absent evm owner hacc (slot + ⟨1⟩)
            (setRewardConfigWithMultiplierMultiplierWord I)
      have hleft :
          sstoreAccountMap owner
              (sstoreAccountMap owner evm.accountMap slot finalWord)
              (slot + ⟨1⟩) (setRewardConfigWithMultiplierMultiplierWord I) =
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
          owner (slot + ⟨1⟩) (setRewardConfigWithMultiplierMultiplierWord I) hcollapseSlot
      have hsource :
          (setRewardConfigSourceFinal evm I rescale shouldUpscale).accountMap =
            sstoreAccountMap owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner
                  (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
                slot finalWord)
              (slot + ⟨1⟩) (setRewardConfigWithMultiplierMultiplierWord I) := by
        have htokenMap :
            (setRewardConfigSourceAfterToken evm I).accountMap =
              sstoreAccountMap owner evm.accountMap slot tokenWord := by
          unfold setRewardConfigSourceAfterToken
          simpa [owner, slot, old, tokenWord] using
            storageStore_accountMap evm owner slot tokenWord
        have htokenEnv :
            (setRewardConfigSourceAfterToken evm I).executionEnv = evm.executionEnv := by
          unfold setRewardConfigSourceAfterToken
          simpa [owner, slot, old, tokenWord] using
            storageStore_executionEnv evm owner slot tokenWord
        have hloadToken :
            Solm.EVM.storageLoad (setRewardConfigSourceAfterToken evm I)
              (setRewardConfigSourceAfterToken evm I).executionEnv.codeOwner slot = tokenWord := by
          unfold setRewardConfigSourceAfterToken
          rw [storageStore_executionEnv]
          simpa [owner, slot, old, tokenWord] using
            storageLoad_storageStore_same_present evm owner hacc slot tokenWord
        have hloadTokenOwner :
            Solm.EVM.storageLoad (setRewardConfigSourceAfterToken evm I)
              evm.executionEnv.codeOwner slot = tokenWord := by
          simpa [htokenEnv] using hloadToken
        have hrescaleMap :
            (setRewardConfigSourceAfterRescale evm I rescale).accountMap =
              sstoreAccountMap owner
                (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord := by
          unfold setRewardConfigSourceAfterRescale
          simp [setRewardConfigSourceAfterToken, owner, slot, old, tokenWord,
            rescaleWord, setRewardConfigSlot0AfterRescale, storageStore_accountMap,
            storageStore_executionEnv,
            storageLoad_storageStore_same_present evm owner hacc slot tokenWord]
        have hrescaleEnv :
            (setRewardConfigSourceAfterRescale evm I rescale).executionEnv = evm.executionEnv := by
          unfold setRewardConfigSourceAfterRescale
          rw [storageStore_executionEnv]
          exact htokenEnv
        have haccToken :
            ∃ acc',
              (setRewardConfigSourceAfterToken evm I).accountMap.find? owner = some acc' := by
          rw [htokenMap]
          unfold sstoreAccountMap
          rw [hacc]
          simp [Option.option]
          exact ⟨_, accountMap_find_insert_self _ _ _⟩
        rcases haccToken with ⟨accToken, haccToken⟩
        have haccTokenOwner :
            (setRewardConfigSourceAfterToken evm I).accountMap.find?
              (setRewardConfigSourceAfterToken evm I).executionEnv.codeOwner = some accToken := by
          simpa [htokenEnv] using haccToken
        have hloadRescale :
            Solm.EVM.storageLoad (setRewardConfigSourceAfterRescale evm I rescale)
              (setRewardConfigSourceAfterRescale evm I rescale).executionEnv.codeOwner slot =
              rescaleWord := by
          unfold setRewardConfigSourceAfterRescale
          rw [storageStore_executionEnv]
          simpa [slot, rescaleWord, setRewardConfigSlot0AfterRescale, hloadToken] using
            storageLoad_storageStore_same_present
              (setRewardConfigSourceAfterToken evm I)
              (setRewardConfigSourceAfterToken evm I).executionEnv.codeOwner
              haccTokenOwner slot rescaleWord
        have hloadRescaleOwner :
            Solm.EVM.storageLoad (setRewardConfigSourceAfterRescale evm I rescale)
              evm.executionEnv.codeOwner slot = rescaleWord := by
          simpa [hrescaleEnv] using hloadRescale
        have hboolMap :
            (setRewardConfigSourceAfterShouldUpscale evm I rescale shouldUpscale).accountMap =
              sstoreAccountMap owner
                (sstoreAccountMap owner
                  (sstoreAccountMap owner evm.accountMap slot tokenWord) slot rescaleWord)
                slot finalWord := by
          unfold setRewardConfigSourceAfterShouldUpscale
          simp [hrescaleMap, hrescaleEnv, hloadRescaleOwner, owner, slot, bit, finalWord,
            rescaleWord, setRewardConfigSlot0Final, setRewardConfigSlot0AfterRescale,
            storageStore_accountMap]
        have hboolEnv :
            (setRewardConfigSourceAfterShouldUpscale evm I rescale shouldUpscale).executionEnv =
              evm.executionEnv := by
          unfold setRewardConfigSourceAfterShouldUpscale
          simp [hrescaleEnv, owner, slot, bit, finalWord, setRewardConfigSlot0Final,
            storageStore_executionEnv]
        unfold setRewardConfigSourceFinal
        simp [hboolMap, hboolEnv, owner, slot, storageStore_accountMap]
      rw [hsource]
      simpa [owner, slot, bit, old, finalWord] using hcollapse

def setRewardConfigAfterDecimalsFrame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  { contract := contract,
    locals :=
      ((setRewardConfigWithMultiplierBodyStore I).insert "accrualScale"
        (.int (Int.ofNat baseWord.toNat))).insert "tokenDecimals" (.int (Int.ofNat decNat)) }

def setRewardConfigAfterPow10Frame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  resumeAfterInternalCall (setRewardConfigAfterDecimalsFrame I baseWord decNat)
    "tokenScale256" (some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])

def setRewardConfigAfterSafe64Frame (I : ExecutionEnv) (baseWord : UInt256)
    (decNat : ℕ) : Frame :=
  resumeAfterInternalCall (setRewardConfigAfterPow10Frame I baseWord decNat)
    "tokenScale" (some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])

theorem evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
    (evm : EVM.State) (I : ExecutionEnv) (field : Ident) {locals : Store}
    (hcomet :
      locals.get? "comet" = some (setRewardConfigWithMultiplierCometValue I)) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (rewardConfigF (.var "comet") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (setRewardConfigWithMultiplierCometWord I).toNat)),
                        .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [hcomet]

theorem setRewardConfigAfterSafe64Frame_rewardConfig_none (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "rewardConfig" = none := by
  simp only [setRewardConfigAfterSafe64Frame, setRewardConfigAfterPow10Frame,
    setRewardConfigAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigWithMultiplierBodyStore_rewardConfig]

theorem setRewardConfigAfterSafe64Frame_comet (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "comet" =
      some (setRewardConfigWithMultiplierCometValue I) := by
  simp only [setRewardConfigAfterSafe64Frame, setRewardConfigAfterPow10Frame,
    setRewardConfigAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigWithMultiplierBodyStore_comet]

theorem setRewardConfigAfterSafe64Frame_accrualScale (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "accrualScale" =
      some (.int (Int.ofNat baseWord.toNat)) := by
  simp only [setRewardConfigAfterSafe64Frame, setRewardConfigAfterPow10Frame,
    setRewardConfigAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setRewardConfigAfterSafe64Frame_tokenScale (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "tokenScale" =
      some (.int (Int.ofNat ((10 : ℕ) ^ decNat))) := by
  simp only [setRewardConfigAfterSafe64Frame, resumeAfterInternalCall, collapseReturns]
  rw [store_get_self]

theorem setRewardConfigAfterSafe64Frame_token (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "token" =
      some (setRewardConfigWithMultiplierTokenValue I) := by
  simp only [setRewardConfigAfterSafe64Frame, setRewardConfigAfterPow10Frame,
    setRewardConfigAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigWithMultiplierBodyStore_token]

theorem setRewardConfigAfterSafe64Frame_multiplier (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    (setRewardConfigAfterSafe64Frame I baseWord decNat).locals.get? "multiplier" =
      some (setRewardConfigWithMultiplierMultiplierValue I) := by
  simp only [setRewardConfigAfterSafe64Frame, setRewardConfigAfterPow10Frame,
    setRewardConfigAfterDecimalsFrame, resumeAfterInternalCall]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    setRewardConfigWithMultiplierBodyStore_multiplier]

theorem setRewardConfigAssign_token_afterSafe64 (evm : EVM.State) (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ)
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus) :
    assignStorageRef? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evm .storage
      (rewardConfigF (.var "comet") "token") (setRewardConfigWithMultiplierTokenValue I) =
      .ok (setRewardConfigAfterSafe64Frame I baseWord decNat,
        setRewardConfigSourceAfterToken evm I) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat
                  (setRewardConfigWithMultiplierCometWord I).toNat)),
                .field "token"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 0 20 (by decide) .address
  have her :
      evalStorageRef config (setRewardConfigAfterSafe64Frame I baseWord decNat) evm
        (rewardConfigF (.var "comet") "token") = .ok er := by
    exact evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
      (evm := evm) (I := I) (field := "token")
      (setRewardConfigAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .address) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore evm loc (setRewardConfigWithMultiplierTokenValue I) =
        some (setRewardConfigSourceAfterToken evm I) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 0 20
      (by decide) .address from rfl, slotAdd_zero]
    simpa [setRewardConfigSourceAfterToken, setRewardConfigSlot0AfterToken,
      setRewardConfigWithMultiplierTokenValue, fieldLoc, loc, addressOffset0Loc] using
      storageLocStore_address_offset0 evm (setRewardConfigWithMultiplierSlotOf I)
        (setRewardConfigWithMultiplierTokenWord I) hcanonToken
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigAfterSafe64Frame I baseWord decNat)
    (evm := evm) (evm' := setRewardConfigSourceAfterToken evm I)
    (slot := rewardConfigF (.var "comet") "token") (er := er)
    (ty := .elem .address) (loc := loc)
    (value := setRewardConfigWithMultiplierTokenValue I)
    (setRewardConfigAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigAssign_rescale_afterSafe64 (evm : EVM.State) (I : ExecutionEnv)
    (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
      (setRewardConfigSourceAfterToken evm I) .storage
      (rewardConfigF (.var "comet") "rescaleFactor") (.int (Int.ofNat rescale.toNat)) =
      .ok (setRewardConfigAfterSafe64Frame I baseWord decNat,
        setRewardConfigSourceAfterRescale evm I rescale) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat
                  (setRewardConfigWithMultiplierCometWord I).toNat)),
                .field "rescaleFactor"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 20 8 (by decide)
      (.int uint64Int)
  have her :
      evalStorageRef config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterToken evm I)
        (rewardConfigF (.var "comet") "rescaleFactor") = .ok er := by
    exact evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
      (evm := setRewardConfigSourceAfterToken evm I) (I := I) (field := "rescaleFactor")
      (setRewardConfigAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint64Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigSourceAfterToken evm I) loc
        (.int (Int.ofNat rescale.toNat)) =
        some (setRewardConfigSourceAfterRescale evm I rescale) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 20 8
      (by decide) (.int uint64Int) from rfl, slotAdd_zero]
    simpa [setRewardConfigSourceAfterRescale] using
      setRewardConfigStorageLocStore_uint64_offset20
        (setRewardConfigSourceAfterToken evm I) (setRewardConfigWithMultiplierSlotOf I) rescale
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigSourceAfterToken evm I)
    (evm' := setRewardConfigSourceAfterRescale evm I rescale)
    (slot := rewardConfigF (.var "comet") "rescaleFactor") (er := er)
    (ty := .elem (.int uint64Int)) (loc := loc)
    (value := .int (Int.ofNat rescale.toNat))
    (setRewardConfigAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigAssign_shouldUpscale_false_afterSafe64 (evm : EVM.State)
    (I : ExecutionEnv) (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
      (setRewardConfigSourceAfterRescale evm I rescale) .storage
      (rewardConfigF (.var "comet") "shouldUpscale") (.bool false) =
      .ok (setRewardConfigAfterSafe64Frame I baseWord decNat,
        setRewardConfigSourceAfterShouldUpscale evm I rescale false) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat
                  (setRewardConfigWithMultiplierCometWord I).toNat)),
                .field "shouldUpscale"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 28 1 (by decide) .bool
  have her :
      evalStorageRef config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterRescale evm I rescale)
        (rewardConfigF (.var "comet") "shouldUpscale") = .ok er := by
    exact evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
      (evm := setRewardConfigSourceAfterRescale evm I rescale) (I := I)
      (field := "shouldUpscale")
      (setRewardConfigAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .bool) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigSourceAfterRescale evm I rescale) loc (.bool false) =
        some (setRewardConfigSourceAfterShouldUpscale evm I rescale false) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 28 1
      (by decide) .bool from rfl, slotAdd_zero]
    simpa [setRewardConfigSourceAfterShouldUpscale] using
      setRewardConfigStorageLocStore_bool_false_offset28
        (setRewardConfigSourceAfterRescale evm I rescale) (setRewardConfigWithMultiplierSlotOf I)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigSourceAfterRescale evm I rescale)
    (evm' := setRewardConfigSourceAfterShouldUpscale evm I rescale false)
    (slot := rewardConfigF (.var "comet") "shouldUpscale") (er := er)
    (ty := .elem .bool) (loc := loc) (value := .bool false)
    (setRewardConfigAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

theorem setRewardConfigAssign_shouldUpscale_true_afterSafe64 (evm : EVM.State)
    (I : ExecutionEnv) (baseWord rescale : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
      (setRewardConfigSourceAfterRescale evm I rescale) .storage
      (rewardConfigF (.var "comet") "shouldUpscale") (.bool true) =
      .ok (setRewardConfigAfterSafe64Frame I baseWord decNat,
        setRewardConfigSourceAfterShouldUpscale evm I rescale true) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat
                  (setRewardConfigWithMultiplierCometWord I).toNat)),
                .field "shouldUpscale"] }
  let loc : StorageLoc :=
    fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 28 1 (by decide) .bool
  have her :
      evalStorageRef config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterRescale evm I rescale)
        (rewardConfigF (.var "comet") "shouldUpscale") = .ok er := by
    exact evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
      (evm := setRewardConfigSourceAfterRescale evm I rescale) (I := I)
      (field := "shouldUpscale")
      (setRewardConfigAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem .bool) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hstore :
      storageLocStore (setRewardConfigSourceAfterRescale evm I rescale) loc (.bool true) =
        some (setRewardConfigSourceAfterShouldUpscale evm I rescale true) := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 0) 28 1
      (by decide) .bool from rfl, slotAdd_zero]
    simpa [setRewardConfigSourceAfterShouldUpscale] using
      setRewardConfigStorageLocStore_bool_true_offset28
        (setRewardConfigSourceAfterRescale evm I rescale) (setRewardConfigWithMultiplierSlotOf I)
  exact assignStorageRef_storage_scalar_value (cfg := config)
    (solm := setRewardConfigAfterSafe64Frame I baseWord decNat)
    (evm := setRewardConfigSourceAfterRescale evm I rescale)
    (evm' := setRewardConfigSourceAfterShouldUpscale evm I rescale true)
    (slot := rewardConfigF (.var "comet") "shouldUpscale") (er := er)
    (ty := .elem .bool) (loc := loc) (value := .bool true)
    (setRewardConfigAfterSafe64Frame_rewardConfig_none I baseWord decNat)
    her hty (by rfl) (by trivial) hstore

set_option maxHeartbeats 5000000 in
theorem setRewardConfigAssign_multiplier_afterSafe64_state (evm : EVM.State) (I : ExecutionEnv)
    (baseWord : UInt256) (decNat : ℕ) :
    assignStorageRef? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
      evm .storage
      (rewardConfigF (.var "comet") "multiplier") (setRewardConfigWithMultiplierMultiplierValue I) =
      .ok (setRewardConfigAfterSafe64Frame I baseWord decNat,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I)) := by
  let er : EvaledStorageRef :=
    { base := "rewardConfig",
      steps := [.mindex (.address (AccountAddress.ofNat
                  (setRewardConfigWithMultiplierCometWord I).toNat)),
                .field "multiplier"] }
  let loc : StorageLoc :=
    uint256Loc (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
  have her :
      evalStorageRef config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        evm
        (rewardConfigF (.var "comet") "multiplier") = .ok er := by
    exact evalStorageRef_setRewardConfigWithMultiplier_rewardConfig_field_of_comet
      (evm := evm) (I := I)
      (field := "multiplier")
      (setRewardConfigAfterSafe64Frame_comet I baseWord decNat)
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout er = fun _ => some loc := by
    rw [show loc = fieldLoc (slotAdd (setRewardConfigWithMultiplierSlotOf I) 1) 0 32
      (by decide) (.int uint256Int) by
        dsimp [loc]
        rw [slotAdd_one]
        rfl]
    rfl
  have hstore :
      storageLocStore evm
        loc (setRewardConfigWithMultiplierMultiplierValue I) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I)) := by
    let slot1 := setRewardConfigWithMultiplierSlotOf I + ⟨1⟩
    change storageLocStore evm
        (uint256Loc slot1)
        (.int (Int.ofNat (setRewardConfigWithMultiplierMultiplierWord I).toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        slot1
        (setRewardConfigWithMultiplierMultiplierWord I))
    exact storageLocStore_uint256 evm slot1 (setRewardConfigWithMultiplierMultiplierWord I)
  have hbase := setRewardConfigAfterSafe64Frame_rewardConfig_none I baseWord decNat
  apply assignStorageRef_storage_scalar_value
      (er := er) (ty := .elem (.int uint256Int)) (loc := loc)
  · exact hbase
  · exact her
  · exact hty
  · exact hloc
  · trivial
  · exact hstore

set_option maxHeartbeats 1000000 in
theorem setRewardConfigWithMultiplierFunctionBodyReturns_downscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = baseWord.toNat / (10 : ℕ) ^ decNat)
    (hgt : (10 : ℕ) ^ decNat < baseWord.toNat) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body
      (.returned (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceFinal evmDec I rescale false) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (.ok (setRewardConfigAfterSafe64Frame I baseWord decNat)
      (setRewardConfigSourceFinal evmDec I rescale false))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigAfterDecimalsFrame, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigAfterPow10Frame, setRewardConfigAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool true) := by
    have hgtInt : (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      exact_mod_cast hgt
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hgtInt
  refine ExecBlock.consNormal (ExecStmt.iteTrue hcond ?_) ExecBlock.nil
  have htokenRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterToken evmDec I)
        (.binary .div (.var "accrualScale") (.var "tokenScale")) =
        .ok (.int (Int.ofNat rescale.toNat)) := by
    rw [hrescale]
    have hpowPos : (10 : ℕ) ^ decNat ≠ 0 := by positivity
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hpowPos]
  refine ExecBlock.consNormal
    (ExecStmt.assign hrescaleRhs
      (setRewardConfigAssign_rescale_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have hfalseRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterRescale evmDec I rescale) (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  refine ExecBlock.consNormal
    (ExecStmt.assign hfalseRhs
      (setRewardConfigAssign_shouldUpscale_false_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have hmultRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterShouldUpscale evmDec I rescale false) (.var "multiplier") =
        .ok (setRewardConfigWithMultiplierMultiplierValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigAfterSafe64Frame_multiplier]
  rw [setRewardConfigSourceFinal_false]
  exact ExecBlock.consNormal
    (ExecStmt.assign hmultRhs
      (setRewardConfigAssign_multiplier_afterSafe64_state
        (setRewardConfigSourceAfterShouldUpscale evmDec I rescale false) I baseWord decNat))
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem setRewardConfigWithMultiplierFunctionBodyReturns_upscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = (10 : ℕ) ^ decNat / baseWord.toNat)
    (hle : baseWord.toNat ≤ (10 : ℕ) ^ decNat)
    (hbaseNZ : baseWord.toNat ≠ 0) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body
      (.returned (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceFinal evmDec I rescale true) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (.ok (setRewardConfigAfterSafe64Frame I baseWord decNat)
      (setRewardConfigSourceFinal evmDec I rescale true))
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigAfterDecimalsFrame, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigAfterPow10Frame, setRewardConfigAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool false) := by
    have hnotNat : ¬ (10 : ℕ) ^ decNat < baseWord.toNat := by omega
    have hnotInt : ¬ (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      intro hlt
      exact hnotNat (by exact_mod_cast hlt)
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hnotInt
  refine ExecBlock.consNormal (ExecStmt.iteFalse hcond ?_) ExecBlock.nil
  have htokenRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterToken evmDec I)
        (.binary .div (.var "tokenScale") (.var "accrualScale")) =
        .ok (.int (Int.ofNat rescale.toNat)) := by
    rw [hrescale]
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hbaseNZ]
  refine ExecBlock.consNormal
    (ExecStmt.assign hrescaleRhs
      (setRewardConfigAssign_rescale_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have htrueRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterRescale evmDec I rescale) (.boolLit true) = .ok (.bool true) := by
    simp [evalExpr?, pure]
  refine ExecBlock.consNormal
    (ExecStmt.assign htrueRhs
      (setRewardConfigAssign_shouldUpscale_true_afterSafe64 evmDec I baseWord rescale decNat)) ?_
  have hmultRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterShouldUpscale evmDec I rescale true) (.var "multiplier") =
        .ok (setRewardConfigWithMultiplierMultiplierValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigAfterSafe64Frame_multiplier]
  rw [setRewardConfigSourceFinal_true]
  exact ExecBlock.consNormal
    (ExecStmt.assign hmultRhs
      (setRewardConfigAssign_multiplier_afterSafe64_state
        (setRewardConfigSourceAfterShouldUpscale evmDec I rescale true) I baseWord decNat))
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem setRewardConfigWithMultiplierFunctionBodyReverts_upscaleZero
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hbase0 : baseWord.toNat = 0) :
    ExecFuncBody config (setRewardConfigWithMultiplierBodyFrame evm I) evm
      setRewardConfigWithMultiplierFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config (setRewardConfigWithMultiplierBodyFrame evm I) evm
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
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_auth_true evm I hgov)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_setRewardConfigWithMultiplier_body_token_zero_true evm I htoken)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_setRewardConfigWithMultiplier_body_comet evm I)
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallBase hdecBase) ?_
  have htokenExpr :
      evalExpr? config
        { contract := contract,
          locals := (setRewardConfigWithMultiplierBodyStore I).insert "accrualScale"
            (.int (Int.ofNat baseWord.toNat)) }
        evmBase (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [store_get_ne _ _ (by decide), setRewardConfigWithMultiplierBodyStore_token]
  refine ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      htokenExpr
      (by simp [evalExpr?, pure])
      (by rfl)
      hcallDec hdecDec) ?_
  have hpowArgs :
      evalExprs? config (setRewardConfigAfterDecimalsFrame I baseWord decNat) evmDec
        [.var "tokenDecimals"] = .ok [.int (Int.ofNat decNat)] := by
    simp only [setRewardConfigAfterDecimalsFrame, evalExprs?, evalExpr?, EvalResult.ofOption,
      EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterDecimalsFrame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "pow10") (retVar := "tokenScale256") (args := [.var "tokenDecimals"])
      (argVals := [.int (Int.ofNat decNat)])
      (callee := pow10Function) (locals := pow10Store decNat)
      (calleeSolm := { contract := contract, locals := pow10Store decNat })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hpowArgs lookupCallable_pow10 (bindParams_pow10 decNat)
      (by simpa using pow10FunctionBodyReturns_le77 evmDec hle77)) ?_
  have hsafeArgs :
      evalExprs? config (setRewardConfigAfterPow10Frame I baseWord decNat) evmDec
        [.var "tokenScale256"] = .ok [.int (Int.ofNat ((10 : ℕ) ^ decNat))] := by
    simp only [setRewardConfigAfterPow10Frame, setRewardConfigAfterDecimalsFrame,
      resumeAfterInternalCall, evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    rw [store_get_self]
    rfl
  refine ExecBlock.consNormal
    (internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigAfterPow10Frame I baseWord decNat)
      (evm := evmDec) (calleeEvm := evmDec)
      (name := "safe64") (retVar := "tokenScale") (args := [.var "tokenScale256"])
      (argVals := [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      (callee := safe64Function) (locals := safe64Store ((10 : ℕ) ^ decNat))
      (calleeSolm := { contract := contract, locals := safe64Store ((10 : ℕ) ^ decNat) })
      (value := some [.int (Int.ofNat ((10 : ℕ) ^ decNat))])
      hsafeArgs lookupCallable_safe64 (bindParams_safe64 ((10 : ℕ) ^ decNat))
      (by simpa using safe64FunctionBodyReturns_le evmDec hsafe64)) ?_
  have hcond :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec
        (.binary .gt (.var "accrualScale") (.var "tokenScale")) = .ok (.bool false) := by
    have hnotNat : ¬ (10 : ℕ) ^ decNat < baseWord.toNat := by
      rw [hbase0]
      exact Nat.not_lt_zero _
    have hnotInt : ¬ (10 : ℤ) ^ decNat < (baseWord.toNat : ℤ) := by
      intro hlt
      exact hnotNat (by exact_mod_cast hlt)
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simpa [evalBinaryOp?] using hnotInt
  refine ExecBlock.consRevert (ExecStmt.iteFalse hcond ?_)
  have htokenRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat) evmDec (.var "token") =
        .ok (setRewardConfigWithMultiplierTokenValue I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [setRewardConfigAfterSafe64Frame_token]
  refine ExecBlock.consNormal
    (ExecStmt.assign htokenRhs
      (setRewardConfigAssign_token_afterSafe64 evmDec I baseWord decNat hcanonToken)) ?_
  have hrescaleRhs :
      evalExpr? config (setRewardConfigAfterSafe64Frame I baseWord decNat)
        (setRewardConfigSourceAfterToken evmDec I)
        (.binary .div (.var "tokenScale") (.var "accrualScale")) = .revert := by
    simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
    repeat rw [← Std.HashMap.get?_eq_getElem?]
    rw [setRewardConfigAfterSafe64Frame_accrualScale,
      setRewardConfigAfterSafe64Frame_tokenScale]
    simp [evalBinaryOp?, hbase0]
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert hrescaleRhs)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReturns_downscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = baseWord.toNat / (10 : ℕ) ^ decNat)
    (hgt : (10 : ℕ) ^ decNat < baseWord.toNat) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body
      (.returned (resumeAfterInternalCall (setRewardConfigWithMultiplierFrame evm I) "_set" none)
        (setRewardConfigSourceFinal evmDec I rescale false) none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        (.ok (resumeAfterInternalCall (setRewardConfigWithMultiplierFrame evm I) "_set" none)
          (setRewardConfigSourceFinal evmDec I rescale false)) := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (calleeEvm := setRewardConfigSourceFinal evmDec I rescale false)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (calleeSolm := setRewardConfigAfterSafe64Frame I baseWord decNat)
      (value := none)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReturns_downscale
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hrescale hgt)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consNormal hstmt ExecBlock.nil)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReturns_upscale
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hrescale : rescale.toNat = (10 : ℕ) ^ decNat / baseWord.toNat)
    (hle : baseWord.toNat ≤ (10 : ℕ) ^ decNat)
    (hbaseNZ : baseWord.toNat ≠ 0) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body
      (.returned (resumeAfterInternalCall (setRewardConfigWithMultiplierFrame evm I) "_set" none)
        (setRewardConfigSourceFinal evmDec I rescale true) none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        (.ok (resumeAfterInternalCall (setRewardConfigWithMultiplierFrame evm I) "_set" none)
          (setRewardConfigSourceFinal evmDec I rescale true)) := by
    exact internalCallFunctionReturn
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (calleeEvm := setRewardConfigSourceFinal evmDec I rescale true)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (calleeSolm := setRewardConfigAfterSafe64Frame I baseWord decNat)
      (value := none)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReturns_upscale
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hrescale hle hbaseNZ)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consNormal hstmt ExecBlock.nil)

theorem cometRewardsSetRewardConfigWithMultiplierBodyReverts_upscaleZero
    (evm evmBase evmDec : EVM.State) (I : ExecutionEnv) {baseOut decOut : ByteArray}
    {baseWord : UInt256} {decNat : ℕ}
    (hcanonToken : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgov :
      UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) solcAddrMask =
        solcSourceWord evm.executionEnv)
    (htoken :
      UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (setRewardConfigWithMultiplierSlotOf I))
          solcAddrMask = ⟨0⟩)
    (hcallBase :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
        "baseAccrualScale" 0 [] (true, evmBase, baseOut) false)
    (hdecBase :
      config.externalABI.decode? "baseAccrualScale" baseOut =
        some [.int (Int.ofNat baseWord.toNat)])
    (hcallDec :
      typedCallViaEVM config evmBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
        "decimals" 0 [] (true, evmDec, decOut) false)
    (hdecDec :
      config.externalABI.decode? "decimals" decOut = some [.int (Int.ofNat decNat)])
    (hle77 : decNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ decNat ≤ 2 ^ 64 - 1)
    (hbase0 : baseWord.toNat = 0) :
    ExecTransitionBody config contract evm (setRewardConfigWithMultiplierStore I)
      setRewardConfigWithMultiplierTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hstmt :
      ExecStmt config (setRewardConfigWithMultiplierFrame evm I) evm
        (.internalCall "setRewardConfigWithMultiplierBody"
          [.var "comet", .var "token", .var "multiplier"] "_set")
        .reverted := by
    exact internalCallFunctionRevert
      (cfg := config) (caller := setRewardConfigWithMultiplierFrame evm I) (evm := evm)
      (name := "setRewardConfigWithMultiplierBody") (retVar := "_set")
      (args := [.var "comet", .var "token", .var "multiplier"])
      (argVals := setRewardConfigWithMultiplierArgs I)
      (callee := setRewardConfigWithMultiplierFunction)
      (locals := setRewardConfigWithMultiplierBodyStore I)
      (evalExprs_setRewardConfigWithMultiplier_args evm I)
      (by simpa [setRewardConfigWithMultiplierFrame] using
        lookupCallable_setRewardConfigWithMultiplierBody)
      (bindParams_setRewardConfigWithMultiplier I)
      (by
        simpa [setRewardConfigWithMultiplierFrame,
          setRewardConfigWithMultiplierBodyFrame] using
          setRewardConfigWithMultiplierFunctionBodyReverts_upscaleZero
            evm evmBase evmDec I hcanonToken hgov htoken hcallBase hdecBase hcallDec hdecDec
            hle77 hsafe64 hbase0)
  simpa [setRewardConfigWithMultiplierTransition, externalEntryGuard, nonpayable,
    calldataSizeGuard] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (setRewardConfigWithMultiplierStore I) hsize)).run
          (ExecBlock.consRevert hstmt)

def setRewardConfigPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

def setRewardConfigInvalidUInt64Selector : UInt256 :=
  UInt256.shiftLeft (⟨0x4809a3⟩ : UInt256) ⟨226⟩

noncomputable def setRewardConfigPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray setRewardConfigPanicSelector).write 0 mem 0 32

noncomputable def setRewardConfigPanicMem (code : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray code).write 0 (setRewardConfigPanicMem0 mem) 4 32

noncomputable def setRewardConfigInvalidUInt64SelectorMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray setRewardConfigInvalidUInt64Selector).write 0 mem 192 32

noncomputable def setRewardConfigInvalidUInt64Mem (n : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray n).write 0 (setRewardConfigInvalidUInt64SelectorMem mem) 196 32

theorem setRewardConfigBasePostCallMem_read128_of_size_ge (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (setRewardConfigBasePostCallMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold setRewardConfigBasePostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  exact write32_read_back out
    (setRewardConfigBaseAccrualScaleCalldataMem I)
    128 hout32 (by exact setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I)

theorem setRewardConfigBasePostCallMem_size_ge160 (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    160 ≤ (setRewardConfigBasePostCallMem I out).size := by
  unfold setRewardConfigBasePostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hout32 houtSize
  rw [hlen]
  rw [write32_eq out (setRewardConfigBaseAccrualScaleCalldataMem I) 128 hout32
    (by exact setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  have hbase := setRewardConfigBaseAccrualScaleCalldataMem_size_ge128 I
  omega

theorem setRewardConfigBasePostCallMem_mload128_haw :
    ¬ (⟨128⟩ : UInt256) ≥ setRewardConfigBasePostCallAw * ⟨32⟩ := by
  native_decide

theorem setRewardConfigBasePostCallMem_mload128_of_size_ge (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setRewardConfigBasePostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ setRewardConfigBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigBasePostCallMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigBasePostCallMem I out) (aw := setRewardConfigBasePostCallAw)
    (off := ⟨128⟩) (memSize := (setRewardConfigBasePostCallMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact lt_of_lt_of_le (by omega)
        (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))
    setRewardConfigBasePostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        setRewardConfigBasePostCallMem_read128_of_size_ge I hout32 houtSize])

noncomputable abbrev setRewardConfigBasePostDecodeMem (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨160⟩ : UInt256)).write 0
    (setRewardConfigBasePostCallMem I out) 64 32

theorem setRewardConfigBasePostDecodeMem_read128_of_size_ge (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (setRewardConfigBasePostDecodeMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  unfold setRewardConfigBasePostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨160⟩ : UInt256))
    (setRewardConfigBasePostCallMem I out) 64 128
    (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))
    (by omega)
    (by
      exact le_trans (by omega)
        (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))]
  exact setRewardConfigBasePostCallMem_read128_of_size_ge I hout32 houtSize

theorem setRewardConfigBasePostDecodeMem_mload128_of_size_ge (I : ExecutionEnv)
    {out : ByteArray} (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (setRewardConfigBasePostDecodeMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ setRewardConfigBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigBasePostDecodeMem I out).readWithPadding
          (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigBasePostDecodeMem I out) (aw := setRewardConfigBasePostCallAw)
    (off := ⟨128⟩) (memSize := (setRewardConfigBasePostDecodeMem I out).size)
    rfl
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      unfold setRewardConfigBasePostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨160⟩ : UInt256))
        (setRewardConfigBasePostCallMem I out) 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))]
      simp
      have hsz := setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize
      omega)
    setRewardConfigBasePostCallMem_mload128_haw
    |>.trans (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        setRewardConfigBasePostDecodeMem_read128_of_size_ge I hout32 houtSize])

theorem setRewardConfigBasePostDecodeMem_mload64 (I : ExecutionEnv) {out : ByteArray}
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setRewardConfigBasePostDecodeMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigBasePostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigBasePostDecodeMem I out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigBasePostCallAw) (v := ⟨160⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigBasePostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨160⟩ : UInt256))
        (setRewardConfigBasePostCallMem I out) 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))]
      simp
      have hsz := setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigBasePostDecodeMem
      rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))]
      rw [show (UInt256.toByteArray (⟨160⟩ : UInt256)).extract 0 32 =
          UInt256.toByteArray (⟨160⟩ : UInt256) by
        rw [show 32 = (UInt256.toByteArray (⟨160⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact byteArray_extract_self _])

theorem decodeReturnValueWithMode_modern_uint64_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint64 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint64])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint64 uint64Int
  rw [if_neg htake0n]
  rfl

theorem decodeReturnValueWithMode_modern_uint64_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : fromByteArrayBigEndian (returndata.extract 0 32) < EVM.twoPow 64) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint64 returndata =
      some (.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint64])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint64 uint64Int
  rw [if_pos htake0]
  simp only [bind, Option.bind]
  rw [List.drop_zero]
  rw [hwordList]
  have hlt256 :
      fromByteArrayBigEndian (returndata.extract 0 32) < UInt256.size :=
    lt_trans hword (by native_decide)
  have hval :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt hlt256
  have hguardNat :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat <
        EVM.twoPow 64 := by
    rw [hval]
    exact hword
  have hguard :
      ↑(UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).val <
        EVM.twoPow 64 := by
    simpa [UInt256.toNat] using hguardNat
  simp [ABI.decodeABIWord?, hguard]
  simpa [UInt256.toNat] using hval

theorem decodeReturnValueWithMode_modern_uint64_none_noncanon {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : ¬ fromByteArrayBigEndian (returndata.extract 0 32) < EVM.twoPow 64) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint64 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint64])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint64 uint64Int
  rw [if_pos htake0]
  simp only [bind, Option.bind]
  rw [List.drop_zero]
  rw [hwordList]
  have hval :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt
      (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hguardNat :
      ¬ (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat <
        EVM.twoPow 64 := by
    intro hlt
    exact hword (by
      rw [← hval]
      exact hlt)
  have hguard :
      ¬ ↑(UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).val <
        EVM.twoPow 64 := by
    simpa [UInt256.toNat] using hguardNat
  simp [ABI.decodeABIWord?, hguard]

theorem decodeReturnValueWithMode_modern_uint64_none_huge {returndata : ByteArray}
    (hhi : 2 ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint64 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint64])
    (returndata := returndata) (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhi⟩)]

theorem decodeReturnValueWithMode_modern_uint8_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint8 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0n : ¬ ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint8])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint8 uint8Int
  rw [if_neg htake0n]
  rfl

theorem decodeReturnValueWithMode_modern_uint8_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : fromByteArrayBigEndian (returndata.extract 0 32) < EVM.twoPow 8) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint8 returndata =
      some (.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint8])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint8 uint8Int
  rw [if_pos htake0]
  simp only [bind, Option.bind]
  rw [List.drop_zero]
  rw [hwordList]
  have hlt256 :
      fromByteArrayBigEndian (returndata.extract 0 32) < UInt256.size :=
    lt_trans hword (by native_decide)
  have hval :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt hlt256
  have hguardNat :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat <
        EVM.twoPow 8 := by
    rw [hval]
    exact hword
  have hguard :
      ↑(UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).val <
        EVM.twoPow 8 := by
    simpa [UInt256.toNat] using hguardNat
  simp [ABI.decodeABIWord?, hguard]
  simpa [UInt256.toNat] using hval

theorem decodeReturnValueWithMode_modern_uint8_none_noncanon {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255)
    (hword : ¬ fromByteArrayBigEndian (returndata.extract 0 32) < EVM.twoPow 8) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint8 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((returndata.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint8])
    (returndata := returndata) (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  simp only [decodeScalarWords?]
  unfold decodeScalarWord? ABI.readWord? ABI.readBytes? uint8 uint8Int
  rw [if_pos htake0]
  simp only [bind, Option.bind]
  rw [List.drop_zero]
  rw [hwordList]
  have hval :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) :=
    UInt256.toNat_ofNat_of_lt
      (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hguardNat :
      ¬ (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat <
        EVM.twoPow 8 := by
    intro hlt
    exact hword (by
      rw [← hval]
      exact hlt)
  have hguard :
      ¬ ↑(UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).val <
        EVM.twoPow 8 := by
    simpa [UInt256.toNat] using hguardNat
  simp [ABI.decodeABIWord?, hguard]

theorem decodeReturnValueWithMode_modern_uint8_none_huge {returndata : ByteArray}
    (hhi : 2 ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValueWithMode? DecodeMode.modern uint8 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (types := [uint8])
    (returndata := returndata) (by decide)]
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhi⟩)]

theorem cometRewardsBaseAccrualScale_decode_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "baseAccrualScale" out = none := by
  change compoundRewardsExternalABI.decode? "baseAccrualScale" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_none_short (returndata := out) hshort)

theorem cometRewardsBaseAccrualScale_decode_ok {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64) :
    config.externalABI.decode? "baseAccrualScale" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] := by
  change compoundRewardsExternalABI.decode? "baseAccrualScale" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))]
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_ok (returndata := out) hlo hhi hword)

theorem cometRewardsBaseAccrualScale_decode_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : ¬ fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64) :
    config.externalABI.decode? "baseAccrualScale" out = none := by
  change compoundRewardsExternalABI.decode? "baseAccrualScale" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_none_noncanon (returndata := out) hlo hhi hword)

theorem cometRewardsBaseAccrualScale_decode_none_huge {out : ByteArray}
    (hhi : 2 ^ 255 ≤ out.size) :
    config.externalABI.decode? "baseAccrualScale" out = none := by
  change compoundRewardsExternalABI.decode? "baseAccrualScale" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint64] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint64_none_huge (returndata := out) hhi)

theorem cometRewardsDecimals_decode_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "decimals" out = none := by
  change compoundRewardsExternalABI.decode? "decimals" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint8] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint8_none_short (returndata := out) hshort)

theorem cometRewardsDecimals_decode_ok {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 8) :
    config.externalABI.decode? "decimals" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))] := by
  change compoundRewardsExternalABI.decode? "decimals" out =
      some [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))]
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint8] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint8_ok (returndata := out) hlo hhi hword)

theorem cometRewardsDecimals_decode_none_noncanon {out : ByteArray}
    (hlo : 32 ≤ out.size) (hhi : out.size < 2 ^ 255)
    (hword : ¬ fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 8) :
    config.externalABI.decode? "decimals" out = none := by
  change compoundRewardsExternalABI.decode? "decimals" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint8] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint8_none_noncanon (returndata := out) hlo hhi hword)

theorem cometRewardsDecimals_decode_none_huge {out : ByteArray}
    (hhi : 2 ^ 255 ≤ out.size) :
    config.externalABI.decode? "decimals" out = none := by
  change compoundRewardsExternalABI.decode? "decimals" out = none
  unfold compoundRewardsExternalABI decodeReturn?
  simpa [uint8] using
    congrArg (fun x => x.map fun v => [v])
      (decodeReturnValueWithMode_modern_uint8_none_huge (returndata := out) hhi)

set_option maxHeartbeats 10000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_revert_configured
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land
      (solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask ≠ ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd197⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_auth_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach
  have hcleanComet :
      UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask =
        setRewardConfigWithMultiplierCometWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hcanon0)
  have hcleanCometLeft :
      UInt256.land solcAddrMask (setRewardConfigWithMultiplierCometWord I) =
        setRewardConfigWithMultiplierCometWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigWithMultiplierCometWord I)]
    exact hcleanComet
  have hslot := setRewardConfigWithMultiplierSlotOf_eq_solc I hcanon0
  have hkeccak := rewardConfigKeccakSlot (setRewardConfigWithMultiplierCometWord I)
  have rd203₀ := evm_run rd197 with [
    dup5, and, dup1, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (setRewardConfigWithMultiplierCometWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [hcleanCometLeft]
        rfl)
      (by decide) (by evm_ov)]
  have rd203 := rd203₀
  rw [hcleanCometLeft] at rd203
  have rd215 := evm_run rd203 with [
    push1 ⟨1⟩, swap5, push1 ⟨32⟩, dup7, dup2,
    raw mstore 0 (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, dup10, push1 ⟨0⟩]
  have rd216₀ := rd215.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost hkeccak (by decide) (by evm_ov)
  have rd216 := rd216₀
  rw [← hslot] at rd216
  obtain ⟨_, _, rd217₀⟩ := rd216.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd217⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨217⟩
      [solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I), solcAddrMask, ⟨32⟩,
        solcAddrMask, setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord] using rd217₀⟩
  have rd218 := evm_run rd217 with [and]
  have rd752 := evm_run rd218 with [
    push2 ⟨752⟩, jumpiT htoken (by native_decide)]
  have rd755 := evm_run rd752 with [
    jumpdest, dup9,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (rewardConfigHashMem_mload64 (setRewardConfigWithMultiplierCometWord I))
      (by decide) (by evm_ov)]
  have rd766 := evm_run rd755 with [
    push4 ⟨977536693⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6
      (setRewardConfigAlreadyConfiguredSelectorMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        unfold setRewardConfigAlreadyConfiguredSelectorMem
        rfl)
      (by decide) (by evm_ov)]
  have rd771 := evm_run rd766 with [
    dup1, dup7, add, dup5, swap1,
    raw mstore 3
      (setRewardConfigAlreadyConfiguredMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show (⟨4⟩ : UInt256) + ⟨128⟩ = ⟨132⟩ from by decide,
          show (⟨132⟩ : UInt256).toNat = 132 from by decide]
        unfold setRewardConfigAlreadyConfiguredMem
        rfl)
      (by decide) (by evm_ov)]
  exact evm_run rd771 with [
    push1 ⟨36⟩, swap1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 10000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_configured_ok
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land
      (solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨222⟩
      [⟨32⟩, solcAddrMask, setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd197⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_auth_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach
  have hcleanComet :
      UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask =
        setRewardConfigWithMultiplierCometWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigWithMultiplierCometWord, calldataWord] using hcanon0)
  have hcleanCometLeft :
      UInt256.land solcAddrMask (setRewardConfigWithMultiplierCometWord I) =
        setRewardConfigWithMultiplierCometWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigWithMultiplierCometWord I)]
    exact hcleanComet
  have hslot := setRewardConfigWithMultiplierSlotOf_eq_solc I hcanon0
  have hkeccak := rewardConfigKeccakSlot (setRewardConfigWithMultiplierCometWord I)
  have rd203₀ := evm_run rd197 with [
    dup5, and, dup1, push1 ⟨0⟩,
    raw mstore 0
      (wordAt0Mem (setRewardConfigWithMultiplierCometWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [hcleanCometLeft]
        rfl)
      (by decide) (by evm_ov)]
  have rd203 := rd203₀
  rw [hcleanCometLeft] at rd203
  have rd215 := evm_run rd203 with [
    push1 ⟨1⟩, swap5, push1 ⟨32⟩, dup7, dup2,
    raw mstore 0 (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup2, dup10, push1 ⟨0⟩]
  have rd216₀ := rd215.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I))
    (UInt256.ofNat 3) (by decide) mem_cost hkeccak (by decide) (by evm_ov)
  have rd216 := rd216₀
  rw [← hslot] at rd216
  obtain ⟨_, _, rd217₀⟩ := rd216.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd217⟩ : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨217⟩
      [solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I), solcAddrMask, ⟨32⟩,
        solcAddrMask, setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigWithMultiplierTokenWord I, ⟨64⟩, ⟨0⟩]
      (rewardConfigHashMem (setRewardConfigWithMultiplierCometWord I))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [solcSlotWord] using rd217₀⟩
  have rd218 := evm_run rd217 with [and]
  rw [htoken] at rd218
  exact ⟨_, _, evm_run rd218 with [push2 ⟨752⟩, jumpiNT (by decide)]⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_call_baseAccrualScale
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land
      (solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) setRewardConfigWithMultiplierPc
      (dispatchArmLastStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ gasArg k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨241⟩
      [gasArg, setRewardConfigWithMultiplierCometWord I, ⟨128⟩, ⟨4⟩, ⟨128⟩,
        ⟨32⟩, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigBaseAccrualScaleCalldataMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd222⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_configured_ok
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hwv hsz100 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd234 := evm_run rd222 with [
    dup9,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (rewardConfigHashMem_mload64 (setRewardConfigWithMultiplierCometWord I))
      (by decide) (by evm_ov),
    push4 ⟨1359440587⟩, push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (setRewardConfigBaseAccrualScaleCalldataMem I)
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        unfold setRewardConfigBaseAccrualScaleCalldataMem
        rfl)
      (by decide) (by evm_ov)]
  have rd240 := evm_run rd234 with [
    swap8, dup2, dup10, dup8, dup2, dup8]
  obtain ⟨gasArg, rd241⟩ := evm_run rd240 with [gas]
  exact ⟨gasArg, _, _, by simpa using rd241⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_call_baseAccrualScale_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ_evm I = solcSourceWord I)
    (htoken : UInt256.land
      (solcSlotWord σ_evm I (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      setRewardConfigWithMultiplierPc (dispatchArmLastStack I) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∃ cA' σ'_evm σ'_solm A'_solm z out k C,
      typedCallViaEVM config
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
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
        ⟨242⟩ (setRewardConfigBasePostCallStack z I)
        (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out
        (cA', σ'_evm) k C ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd241⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_call_baseAccrualScale
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd241Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨241⟩
        (gasArg :: setRewardConfigWithMultiplierCometWord I :: ⟨128⟩ :: ⟨4⟩ ::
          ⟨128⟩ :: ⟨32⟩ :: setRewardConfigBasePostCallTail I)
        (setRewardConfigBaseAccrualScaleCalldataMem I)
        (UInt256.ofNat 5) ByteArray.empty (cA, σ_evm) k0 C0 := by
    simpa [setRewardConfigBasePostCallTail] using rd241
  have hdecCall :
      decode cometRewardsBytecode (⟨241⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  obtain ⟨cA', σ'_evm, z, out, A_in, callGas, k', C', hΘ, rd242, _houtSize⟩ :=
    RD.uniswapStaticcall (t := setRewardConfigBasePostCallTail I) rd241Call hdecCall
      hdepth (by simp [setRewardConfigBasePostCallTail])
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
      (r := AccountAddress.ofUInt256 (setRewardConfigWithMultiplierCometWord I))
      (c := toExecute σ_evm
        (AccountAddress.ofUInt256 (setRewardConfigWithMultiplierCometWord I)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (setRewardConfigBaseAccrualScaleCalldataMem I).readWithPadding 128 4)
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
  have htgt := setRewardConfigBaseTarget_eq_targetWord I
  have hcd := setRewardConfigBaseAccrualScaleCalldataMem_encode I
  have hcallE :
      typedCallViaEVM config
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierCometWord I).toNat))
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
      (tgt := EVM.address (AccountAddress.ofNat
        (setRewardConfigWithMultiplierCometWord I).toNat))
      (targetWord := setRewardConfigWithMultiplierCometWord I)
      (cA' := cA') (σ' := σ'_evm) (A' := A'_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := setRewardConfigBaseAccrualScaleCalldataMem I)
      (inOff := ⟨128⟩) (inSize := ⟨4⟩) (callPerm := false)
      hdepthNe htgt hcd ?_
    simpa [initState] using hΘeq
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_initState_accountMapEquiv hcallE hAccounts
  exact ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, k', C',
    hcallSolm, hPostAccounts, by
      simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail,
        setRewardConfigBasePostCallMem, setRewardConfigBasePostCallAw] using rd242,
    houtSign⟩

theorem rdSwap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f x h i j : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: x :: h :: i :: j :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (j :: b :: c :: d :: e :: f :: x :: h :: i :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun s hc hp hs => by
    have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
      rw [hc, hp]
      exact hdec
    rw [← hc, step_swap9 s hd, hs]
    have hov' :
        ¬ ((a :: b :: c :: d :: e :: f :: x :: h :: i :: j :: t).length - 10 + 10 >
            1024) := by
      simp only [List.length_cons]
      omega
    simp only [if_neg hov', GasConstants.Gverylow, stSwap])

theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length - 12
        + 13 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem rdDup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_failure
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩ (setRewardConfigBasePostCallStack false I)
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd242 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩
      [⟨0⟩, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C := by
    simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail] using rd
  have rd243 := rdSwap9 rd242 (by native_decide) (by simp)
  have rd741 := evm_run rd243 with [
    dup10, iszero, push2 ⟨741⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd744 := evm_run rd741 with [
    jumpdest, dup11,
    raw mload 0 ⟨128⟩ setRewardConfigBasePostCallAw (by native_decide)
      mem_cost (setRewardConfigBasePostCallMem_mload64 I houtSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have rd748pre := evm_run rd744 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    out.write 0 (setRewardConfigBasePostCallMem I out) 128 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigBasePostCallAw.toNat 128 rdsz.toNat)
  have rd748 := RD.returndatacopy
    (Cₘ aw2 - Cₘ setRewardConfigBasePostCallAw) mem2 aw2 rd748pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by rfl)
    (by rfl)
    (by simp)
  have rd751 := evm_run rd748 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 128 rdsz.toNat)) - Cₘ aw2)
    rd751 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from rfl])
    (by simp)

abbrev setRewardConfigBaseReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev setRewardConfigAfterBaseDecodeStack (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [solcAddrMask, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
    setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
    setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, baseWord, ⟨64⟩, ⟨0⟩]

abbrev setRewardConfigDecimalsSelectorWord : UInt256 := ⟨826074471⟩

abbrev setRewardConfigDecimalsSelectorShifted : UInt256 :=
  UInt256.shiftLeft setRewardConfigDecimalsSelectorWord ⟨224⟩

noncomputable def setRewardConfigDecimalsCalldataMem
    (I : ExecutionEnv) (baseOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray setRewardConfigDecimalsSelectorShifted).write 0
    (setRewardConfigBasePostDecodeMem I baseOut) 160 32

theorem setRewardConfigDecimalsCalldataMem_read160_4
    (I : ExecutionEnv) (baseOut : ByteArray) :
    (setRewardConfigDecimalsCalldataMem I baseOut).readWithPadding 160 4 =
      decimalsSelector := by
  unfold setRewardConfigDecimalsCalldataMem
  rw [toByteArray_write_read_window_of_gap
    (b := setRewardConfigDecimalsSelectorShifted)
    (mem := setRewardConfigBasePostDecodeMem I baseOut)
    (off := 160) (start := 0) (len := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))]
  native_decide

theorem setRewardConfigDecimalsCalldataMem_encode
    (I : ExecutionEnv) (baseOut : ByteArray) :
    config.externalABI.encode? "decimals" [] =
      some ((setRewardConfigDecimalsCalldataMem I baseOut).readWithPadding 160 4) := by
  rw [setRewardConfigDecimalsCalldataMem_read160_4]
  rfl

abbrev setRewardConfigDecimalsTargetWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (setRewardConfigWithMultiplierTokenWord I)

theorem setRewardConfigDecimalsTarget_eq_targetWord (I : ExecutionEnv)
    (hcanon : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus) :
    EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat) =
      AccountAddress.ofUInt256 (setRewardConfigDecimalsTargetWord I) := by
  have hcleanLeft :
      UInt256.land (setRewardConfigWithMultiplierTokenWord I) solcAddrMask =
        setRewardConfigWithMultiplierTokenWord I := by
    exact solcAddrMask_clean (by
      simpa [setRewardConfigWithMultiplierTokenWord, calldataWord] using hcanon)
  have hclean :
      UInt256.land solcAddrMask (setRewardConfigWithMultiplierTokenWord I) =
        setRewardConfigWithMultiplierTokenWord I := by
    rw [u256_land_comm solcAddrMask (setRewardConfigWithMultiplierTokenWord I), hcleanLeft]
  rw [setRewardConfigDecimalsTargetWord, hclean, accountAddress_ofUInt256_eq_ofNat_toNat]
  apply Fin.ext
  simp [EVM.address, EVM.uintN]
  exact Nat.mod_eq_of_lt (AccountAddress.ofNat
    (setRewardConfigWithMultiplierTokenWord I).toNat).isLt

abbrev setRewardConfigDecimalsCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M setRewardConfigBasePostCallAw.toNat 160 32)

abbrev setRewardConfigDecimalsPostCallAw : UInt256 :=
  UInt256.ofNat (MachineState.M
    (MachineState.M setRewardConfigDecimalsCallAw.toNat 160 4) 160 32)

abbrev setRewardConfigDecimalsPostCallTail (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  [⟨160⟩, baseWord, ⟨32⟩, solcAddrMask, setRewardConfigWithMultiplierCometWord I,
    ⟨224⟩, ⟨4⟩, setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
    setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]

abbrev setRewardConfigDecimalsPostCallStack (z : Bool) (baseWord : UInt256)
    (I : ExecutionEnv) : List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) :: setRewardConfigDecimalsPostCallTail baseWord I

noncomputable abbrev setRewardConfigDecimalsPostCallMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  decOut.write 0 (setRewardConfigDecimalsCalldataMem I baseOut) 160
    (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat

theorem byteArray_write_size_ge_base_of_le (src base : ByteArray) {dest len : ℕ}
    (hsrc : len ≤ src.size) (hdest : dest ≤ base.size) :
    base.size ≤ (src.write 0 base dest len).size := by
  by_cases hlen : len = 0
  · subst len
    rw [byteArray_write_len_zero]
  · by_cases hin : dest + len ≤ base.size
    · rw [write_eq_gen src base dest len hlen hsrc hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · have hext : base.size < dest + len := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend src base dest len hlen hsrc hdest hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega

theorem setRewardConfigBasePostDecodeMem_read64
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    (setRewardConfigBasePostDecodeMem I baseOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigBasePostDecodeMem
  rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize))]
  rw [show (UInt256.toByteArray (⟨160⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨160⟩ : UInt256) by
    rw [show 32 = (UInt256.toByteArray (⟨160⟩ : UInt256)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem setRewardConfigBasePostDecodeMem_size_ge160
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    160 ≤ (setRewardConfigBasePostDecodeMem I baseOut).size := by
  unfold setRewardConfigBasePostDecodeMem
  exact le_trans (setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize)
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨160⟩ : UInt256))
      (setRewardConfigBasePostCallMem I baseOut) (by rw [toByteArray_size])
      (by
        have hbase := setRewardConfigBasePostCallMem_size_ge160 I hout32 houtSize
        omega))

theorem setRewardConfigDecimalsCalldataMem_size_ge192
    (I : ExecutionEnv) (baseOut : ByteArray) :
    192 ≤ (setRewardConfigDecimalsCalldataMem I baseOut).size := by
  unfold setRewardConfigDecimalsCalldataMem
  exact toByteArray_write_size_ge_off_add32 setRewardConfigDecimalsSelectorShifted
    (setRewardConfigBasePostDecodeMem I baseOut) 160
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))

theorem setRewardConfigDecimalsCalldataMem_read64
    (I : ExecutionEnv) {baseOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    (setRewardConfigDecimalsCalldataMem I baseOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigDecimalsCalldataMem
  rw [toByteArray_write_read_below_of_gap
    (b := setRewardConfigDecimalsSelectorShifted)
    (mem := setRewardConfigBasePostDecodeMem I baseOut)
    (off := 160) (read := 64)
    (by
      exact le_trans (by omega)
        (setRewardConfigBasePostDecodeMem_size_ge160 I hout32 houtSize))
    (by norm_num)
    (by
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_usize 160 (by norm_num)))]
  exact setRewardConfigBasePostDecodeMem_read64 I hout32 houtSize

theorem setRewardConfigDecimalsPostCallMem_size_ge96
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (hdecSize : decOut.size < UInt256.size) :
    96 ≤ (setRewardConfigDecimalsPostCallMem I baseOut decOut).size := by
  unfold setRewardConfigDecimalsPostCallMem
  have hbase := setRewardConfigDecimalsCalldataMem_size_ge192 I baseOut
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat ≤ decOut.size :=
    setRewardConfigBasePostCallLen_le_out_size hdecSize
  exact le_trans (by omega)
    (byteArray_write_size_ge_base_of_le decOut
      (setRewardConfigDecimalsCalldataMem I baseOut) hlen (by omega))

theorem setRewardConfigDecimalsPostCallMem_read64
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigDecimalsPostCallMem I baseOut decOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  unfold setRewardConfigDecimalsPostCallMem
  by_cases hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 0
  · rw [hlen, byteArray_write_len_zero]
    exact setRewardConfigDecimalsCalldataMem_read64 I hout32 houtSize
  · have hsrc :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat ≤ decOut.size :=
      setRewardConfigBasePostCallLen_le_out_size hdecSize
    rw [write_read_below_gen_extend decOut (setRewardConfigDecimalsCalldataMem I baseOut)
      160 (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat 64
      hlen hsrc (by
        have hbase := setRewardConfigDecimalsCalldataMem_size_ge192 I baseOut
        omega)
      (by norm_num)]
    exact setRewardConfigDecimalsCalldataMem_read64 I hout32 houtSize

theorem setRewardConfigDecimalsPostCallMem_mload64
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setRewardConfigDecimalsPostCallMem I baseOut decOut).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigDecimalsPostCallMem I baseOut decOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigDecimalsPostCallAw) (v := ⟨160⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hge := setRewardConfigDecimalsPostCallMem_size_ge96 I (baseOut := baseOut)
        (decOut := decOut) hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact setRewardConfigDecimalsPostCallMem_read64 I hout32 houtSize hdecSize)

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_decode_ok
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩ (setRewardConfigBasePostCallStack true I)
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hbase64 : (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64) :
    ∃ k' C', RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨256⟩
      (setRewardConfigAfterBaseDecodeStack (setRewardConfigBaseReturnWord out) I)
      (setRewardConfigBasePostDecodeMem I out) setRewardConfigBasePostCallAw out acc k' C' := by
  let baseWord : UInt256 := setRewardConfigBaseReturnWord out
  have hbase64' : baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have rd242 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩
      [⟨1⟩, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C := by
    simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail] using rd
  have rd243 := rdSwap9 rd242 (by native_decide) (by simp)
  have rd692 := evm_run rd243 with [
    dup10, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap10, push2 ⟨692⟩, jumpiT (by native_decide) (by jump_dest)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd708₀ := evm_run rd692 with [
    jumpdest, dup4, swap2, swap10, pop, push2 ⟨727⟩, swap1, dup4,
    returndatasize, dup6, gt]
  have rd708 := rd708₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd708
  have rd3071 := evm_run rd708 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigBasePostDecodeMem I out) setRewardConfigBasePostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigBasePostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord setRewardConfigBasePostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord, setRewardConfigBaseReturnWord] using
          setRewardConfigBasePostDecodeMem_mload128_of_size_ge I hout32 houtSize)
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
  have rd727 := evm_run rd3129zero with [
    push2 ⟨1004⟩, jumpiNT (by native_decide), swap1, jump (by jump_dest)]
  have rd728 := evm_run rd727 with [jumpdest]
  have rd729 := rdSwap9 rd728 (by native_decide) (by simp)
  have rd256 := evm_run rd729 with [swap1, push2 ⟨256⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [baseWord, setRewardConfigAfterBaseDecodeStack,
      setRewardConfigBaseReturnWord] using rd256⟩

noncomputable abbrev setRewardConfigBasePostShortDecodeMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.toByteArray ((⟨128⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat out.size + ⟨31⟩))).write 0
      (setRewardConfigBasePostCallMem I out) 64 32

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩ (setRewardConfigBasePostCallStack true I)
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C)
    (hshort : out.size < 32) (houtSize : out.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨1⟩ := by
    apply ugt_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hshort
  have rd242 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩
      [⟨1⟩, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C := by
    simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail] using rd
  have rd243 := rdSwap9 rd242 (by native_decide) (by simp)
  have rd692 := evm_run rd243 with [
    dup10, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap10, push2 ⟨692⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd708₀ := evm_run rd692 with [
    jumpdest, dup4, swap2, swap10, pop, push2 ⟨727⟩, swap1, dup4,
    returndatasize, dup6, gt]
  have rd708 := rd708₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd708
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
  have rd3071 := evm_run rd708 with [
    push2 ⟨734⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨709⟩, jump (by jump_dest),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigBasePostShortDecodeMem I out) setRewardConfigBasePostCallAw
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
theorem cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩ (setRewardConfigBasePostCallStack true I)
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C)
    (hout32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hbase64 : ¬ (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let baseWord : UInt256 := setRewardConfigBaseReturnWord out
  have hbase64' : ¬ baseWord.toNat < EVM.twoPow 64 := by
    simpa [baseWord] using hbase64
  have rd242 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨242⟩
      [⟨1⟩, setRewardConfigWithMultiplierTokenWord I, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩, ⟨128⟩, ⟨64⟩, ⟨0⟩]
      (setRewardConfigBasePostCallMem I out) setRewardConfigBasePostCallAw out acc k C := by
    simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail] using rd
  have rd243 := rdSwap9 rd242 (by native_decide) (by simp)
  have rd692 := evm_run rd243 with [
    dup10, iszero, push2 ⟨741⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap10, push2 ⟨692⟩, jumpiT (by native_decide) (by jump_dest)]
  let rdsz : UInt256 := UInt256.ofNat out.size
  have hrdsz_toNat : rdsz.toNat = out.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt houtSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hout32
  have rd708₀ := evm_run rd692 with [
    jumpdest, dup4, swap2, swap10, pop, push2 ⟨727⟩, swap1, dup4,
    returndatasize, dup6, gt]
  have rd708 := rd708₀
  rw [show UInt256.ofNat out.size = rdsz from rfl, hgt] at rd708
  have rd3071 := evm_run rd708 with [
    push2 ⟨734⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨719⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide),
    push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigBasePostDecodeMem I out) setRewardConfigBasePostCallAw
      (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigBasePostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd3106 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, swap1, push2 ⟨3106⟩,
    jump (by jump_dest), jumpdest, swap1, dup2, push1 ⟨32⟩, swap2, sub,
    slt, push2 ⟨1004⟩, jumpiNT (by native_decide)]
  have rd3129 := evm_run rd3106 with [
    raw mload 0 baseWord setRewardConfigBasePostCallAw (by native_decide)
      mem_cost
      (by
        simpa [baseWord, setRewardConfigBaseReturnWord] using
          setRewardConfigBasePostDecodeMem_mload128_of_size_ge I hout32 houtSize)
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

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_call_decimals
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut : ByteArray} {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨256⟩
      (setRewardConfigAfterBaseDecodeStack baseWord I)
      (setRewardConfigBasePostDecodeMem I baseOut) setRewardConfigBasePostCallAw
      baseOut acc k C)
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    ∃ gasArg k' C', RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨279⟩
      [gasArg, setRewardConfigDecimalsTargetWord I, ⟨160⟩, ⟨4⟩, ⟨160⟩,
        ⟨32⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsCalldataMem I baseOut) setRewardConfigDecimalsCallAw
      baseOut acc k' C' := by
  have rd262₀ := evm_run rd with [
    jumpdest, pop, dup3, and, swap8, dup10]
  obtain ⟨k262, C262, rd262⟩ : ∃ k262 C262,
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨262⟩
        [⟨64⟩, baseWord, ⟨32⟩, solcAddrMask,
          setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
          setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
          setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigBasePostDecodeMem I baseOut) setRewardConfigBasePostCallAw
        baseOut acc k262 C262 := by
    exact ⟨_, _, by
      simpa [setRewardConfigAfterBaseDecodeStack, setRewardConfigDecimalsTargetWord,
        u256_land_comm] using rd262₀⟩
  have rd263 := evm_run rd262 with [
    raw mload 0 ⟨160⟩ setRewardConfigBasePostCallAw (by native_decide)
      mem_cost
      (setRewardConfigBasePostDecodeMem_mload64 I hout32 houtSize)
      (by native_decide) (by evm_ov)]
  have rd273 := evm_run rd263 with [
    push4 ⟨826074471⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 3 (setRewardConfigDecimalsCalldataMem I baseOut)
      setRewardConfigDecimalsCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
        unfold setRewardConfigDecimalsCalldataMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd278 := evm_run rd273 with [
    dup3, dup2, dup9, dup2, dup14]
  obtain ⟨gasArg, rd279⟩ := evm_run rd278 with [gas]
  exact ⟨gasArg, _, _, by simpa [setRewardConfigDecimalsTargetWord] using rd279⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_call_decimals_made
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {baseOut : ByteArray} {baseWord : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm σ'_solm : AccountMap}
    {A'_solm : Substate} {k C : ℕ}
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth.val < 1024)
    (hPostAccounts : accountMapEquiv σ'_evm σ'_solm)
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨256⟩
      (setRewardConfigAfterBaseDecodeStack baseWord I)
      (setRewardConfigBasePostDecodeMem I baseOut) setRewardConfigBasePostCallAw
      baseOut (cA', σ'_evm) k C)
    (hout32 : 32 ≤ baseOut.size) (houtSize : baseOut.size < UInt256.size) :
    ∃ cA'' σ''_evm σ''_solm A''_solm z out k' C',
      typedCallViaEVM config
        { initState cA gh bl σ_solm σ₀ g A I with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' }
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
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
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨280⟩
        (setRewardConfigDecimalsPostCallStack z baseWord I)
        (setRewardConfigDecimalsPostCallMem I baseOut out) setRewardConfigDecimalsPostCallAw
        out (cA'', σ''_evm) k' C' ∧
      out.size < 2 ^ 255 := by
  obtain ⟨gasArg, k0, C0, rd279⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_call_decimals
      (rd := rd) hout32 houtSize
  have rd279Call :
      RD cometRewardsBytecode I g (initState cA gh bl σ_evm σ₀ g A I) ⟨279⟩
        (gasArg :: setRewardConfigDecimalsTargetWord I :: ⟨160⟩ :: ⟨4⟩ ::
          ⟨160⟩ :: ⟨32⟩ :: setRewardConfigDecimalsPostCallTail baseWord I)
        (setRewardConfigDecimalsCalldataMem I baseOut) setRewardConfigDecimalsCallAw
        baseOut (cA', σ'_evm) k0 C0 := by
    simpa [setRewardConfigDecimalsPostCallTail] using rd279
  have hdecCall :
      decode cometRewardsBytecode (⟨279⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  obtain ⟨cA'', σ''_evm, z, out, A_in, callGas, k', C', hΘ, rd280, _houtSize⟩ :=
    RD.uniswapStaticcall (t := setRewardConfigDecimalsPostCallTail baseWord I)
      rd279Call hdecCall hdepth (by simp [setRewardConfigDecimalsPostCallTail])
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
      (r := AccountAddress.ofUInt256 (setRewardConfigDecimalsTargetWord I))
      (c := toExecute σ'_evm
        (AccountAddress.ofUInt256 (setRewardConfigDecimalsTargetWord I)))
      (g := callGas) (p := UInt256.ofNat I.gasPrice)
      (v := ⟨0⟩) (v' := ⟨0⟩)
      (d := (setRewardConfigDecimalsCalldataMem I baseOut).readWithPadding 160 4)
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
  have htgt := setRewardConfigDecimalsTarget_eq_targetWord I hcanon1
  have hcd := setRewardConfigDecimalsCalldataMem_encode I baseOut
  have hcallE :
      typedCallViaEVM config evmEBase
        (EVM.address (AccountAddress.ofNat (setRewardConfigWithMultiplierTokenWord I).toNat))
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
      (tgt := EVM.address (AccountAddress.ofNat
        (setRewardConfigWithMultiplierTokenWord I).toNat))
      (targetWord := setRewardConfigDecimalsTargetWord I)
      (cA' := cA'') (σ' := σ''_evm) (A' := A''_evm) (A_in := A_in)
      (z := z) (o := out) (g'' := g'') (callGas := callGas)
      (mem := setRewardConfigDecimalsCalldataMem I baseOut)
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
      simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail,
      setRewardConfigDecimalsPostCallMem, setRewardConfigDecimalsPostCallAw] using rd280,
    houtSign⟩

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_failure
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack false baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
    (hbase32 : 32 ≤ baseOut.size) (hbaseSize : baseOut.size < UInt256.size)
    (hdecSize : decOut.size < UInt256.size) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨0⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd681 := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiT (by native_decide) (by jump_dest)]
  have rd682 := evm_run rd681 with [jumpdest]
  have rd683 := rdDup12 rd682 (by native_decide) (by simp)
  have rd684 := evm_run rd683 with [
    raw mload 0 ⟨160⟩ setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigDecimalsPostCallMem_mload64 I hbase32 hbaseSize hdecSize)
      (by native_decide) (by evm_ov)]
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have rd688pre := evm_run rd684 with [returndatasize, push1 ⟨0⟩, dup3]
  let mem2 : ByteArray :=
    decOut.write 0 (setRewardConfigDecimalsPostCallMem I baseOut decOut) 160 rdsz.toNat
  let aw2 : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigDecimalsPostCallAw.toNat 160 rdsz.toNat)
  have rd688 := RD.returndatacopy
    (Cₘ aw2 - Cₘ setRewardConfigDecimalsPostCallAw) mem2 aw2 rd688pre
    (by native_decide)
    (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hrdsz_toNat]; omega)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2, rdsz]
      rw [show (⟨160⟩ : UInt256).toNat = 160 from rfl])
    (by rfl)
    (by rfl)
    (by simp)
  have rd691 := evm_run rd688 with [returndatasize, swap1]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw2.toNat 160 rdsz.toNat)) - Cₘ aw2)
    rd691 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, rdsz]
      rw [show (⟨160⟩ : UInt256).toNat = 160 from rfl])
    (by simp)

noncomputable abbrev setRewardConfigDecimalsPostShortDecodeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray ((⟨160⟩ : UInt256) +
    UInt256.land (UInt256.lnot ⟨31⟩) (UInt256.ofNat decOut.size + ⟨31⟩))).write 0
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) 64 32

noncomputable abbrev setRewardConfigDecimalsPostDecodeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨192⟩ : UInt256)).write 0
    (setRewardConfigDecimalsPostCallMem I baseOut decOut) 64 32

theorem setRewardConfigDecimalsPostCallMem_read160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigDecimalsPostCallMem I baseOut decOut).readWithPadding 160 32 =
      decOut.extract 0 32 := by
  unfold setRewardConfigDecimalsPostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := decOut.size)
      (by decide) hdec32 hdecSize
  rw [hlen]
  rw [write32_read_back decOut (setRewardConfigDecimalsCalldataMem I baseOut) 160
    (by exact hdec32)
    (by
      have hbase := setRewardConfigDecimalsCalldataMem_size_ge192 I baseOut
      omega)]

theorem setRewardConfigDecimalsPostCallMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigDecimalsPostCallMem I baseOut decOut).size := by
  unfold setRewardConfigDecimalsPostCallMem
  have hbase := setRewardConfigDecimalsCalldataMem_size_ge192 I baseOut
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat decOut.size)).toNat = 32 := by
    simpa using umin_ofNat_right_toNat_of_ge (c := 32) (n := decOut.size)
      (by decide) hdec32 hdecSize
  rw [hlen]
  exact le_trans hbase
    (byteArray_write_size_ge_base_of_le decOut
      (setRewardConfigDecimalsCalldataMem I baseOut) hdec32 (by omega))

theorem setRewardConfigDecimalsPostDecodeMem_read160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigDecimalsPostDecodeMem I baseOut decOut).readWithPadding 160 32 =
      decOut.extract 0 32 := by
  unfold setRewardConfigDecimalsPostDecodeMem
  rw [write32_read_above (UInt256.toByteArray (⟨192⟩ : UInt256))
    (setRewardConfigDecimalsPostCallMem I baseOut decOut) 64 160
    (by rw [toByteArray_size])
    (by
      exact le_trans (by omega)
        (setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
          hdec32 hdecSize))
    (by omega)
    (by
      exact le_trans (by omega)
        (setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
          hdec32 hdecSize))]
  exact setRewardConfigDecimalsPostCallMem_read160_of_size_ge I hdec32 hdecSize

theorem setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥
          (setRewardConfigDecimalsPostDecodeMem I baseOut decOut).size
        ∨ (⟨160⟩ : UInt256) ≥ setRewardConfigDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigDecimalsPostDecodeMem I baseOut decOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (decOut.extract 0 32)) := by
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
    (aw := setRewardConfigDecimalsPostCallAw)
    (off := ⟨160⟩)
    (memSize := (setRewardConfigDecimalsPostDecodeMem I baseOut decOut).size)
    rfl
    (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
      unfold setRewardConfigDecimalsPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨192⟩ : UInt256))
        (setRewardConfigDecimalsPostCallMem I baseOut decOut) 64
        (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      simp
      have hsz := setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
        hdec32 hdecSize
      omega)
    (by native_decide)
    |>.trans (by
      rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
        setRewardConfigDecimalsPostDecodeMem_read160_of_size_ge I hdec32 hdecSize])

theorem setRewardConfigDecimalsPostDecodeMem_mload64_of_size_ge
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setRewardConfigDecimalsPostDecodeMem I baseOut decOut).size
        ∨ (⟨64⟩ : UInt256) ≥ setRewardConfigDecimalsPostCallAw * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigDecimalsPostDecodeMem I baseOut decOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨192⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setRewardConfigDecimalsPostCallAw) (v := ⟨192⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigDecimalsPostDecodeMem
      rw [write32_eq (UInt256.toByteArray (⟨192⟩ : UInt256))
        (setRewardConfigDecimalsPostCallMem I baseOut decOut) 64
        (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      simp
      have hsz := setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut)
        hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      unfold setRewardConfigDecimalsPostDecodeMem
      rw [write32_read_back _ _ 64 (by rw [toByteArray_size])
        (by
          exact le_trans (by omega)
            (setRewardConfigDecimalsPostCallMem_size_ge192 I hdec32 hdecSize))]
      rw [show (UInt256.toByteArray (⟨192⟩ : UInt256)).extract 0 32 =
          UInt256.toByteArray (⟨192⟩ : UInt256) by
        rw [show 32 = (UInt256.toByteArray (⟨192⟩ : UInt256)).size by
          rw [toByteArray_size]]
        exact byteArray_extract_self _])

abbrev setRewardConfigDecimalsReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem setRewardConfigDecimalsPostDecodeMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigDecimalsPostDecodeMem I baseOut decOut).size := by
  unfold setRewardConfigDecimalsPostDecodeMem
  exact le_trans
    (setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut) hdec32 hdecSize)
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨192⟩ : UInt256))
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) (by rw [toByteArray_size])
      (by
        have hbase :=
          setRewardConfigDecimalsPostCallMem_size_ge192 I (baseOut := baseOut) hdec32 hdecSize
        omega))

noncomputable def setRewardConfigSuccessFreeMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigDecimalsPostDecodeMem I baseOut decOut) 64 ⟨320⟩

noncomputable def setRewardConfigSuccessTokenMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigSuccessFreeMem I baseOut decOut) 192
    (setRewardConfigDecimalsTargetWord I)

noncomputable def setRewardConfigSuccessRescaleMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigSuccessTokenMem I baseOut decOut) 224 rescale

noncomputable def setRewardConfigSuccessBitMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigSuccessRescaleMem I baseOut decOut rescale) 256 bit

noncomputable def setRewardConfigSuccessMultiplierMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (setRewardConfigSuccessBitMem I baseOut decOut rescale bit) 288
    (setRewardConfigWithMultiplierMultiplierWord I)

noncomputable def setRewardConfigSuccessCometMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (setRewardConfigSuccessMultiplierMem I baseOut decOut rescale bit)
    0 (setRewardConfigWithMultiplierCometWord I)

noncomputable def setRewardConfigSuccessArgsMem
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (setRewardConfigSuccessCometMem I baseOut decOut rescale bit) 32 ⟨1⟩

theorem setRewardConfigSuccessFreeMem_size_ge192
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    192 ≤ (setRewardConfigSuccessFreeMem I baseOut decOut).size := by
  unfold setRewardConfigSuccessFreeMem Reasoning.Theory.writeWord
  have hbase := setRewardConfigDecimalsPostDecodeMem_size_ge192 I (baseOut := baseOut)
    hdec32 hdecSize
  exact le_trans hbase
    (byteArray_write_size_ge_base_of_le (UInt256.toByteArray (⟨320⟩ : UInt256))
      (setRewardConfigDecimalsPostDecodeMem I baseOut decOut) (by rw [toByteArray_size])
      (by omega))

theorem setRewardConfigSuccessTokenMem_size_ge224
    (I : ExecutionEnv) {baseOut decOut : ByteArray}
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    224 ≤ (setRewardConfigSuccessTokenMem I baseOut decOut).size := by
  have hfree := setRewardConfigSuccessFreeMem_size_ge192 I (baseOut := baseOut)
    hdec32 hdecSize
  unfold setRewardConfigSuccessTokenMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num))

theorem setRewardConfigSuccessRescaleMem_size_ge256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    256 ≤ (setRewardConfigSuccessRescaleMem I baseOut decOut rescale).size := by
  have htoken := setRewardConfigSuccessTokenMem_size_ge224 I (baseOut := baseOut)
    hdec32 hdecSize
  unfold setRewardConfigSuccessRescaleMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))

theorem setRewardConfigSuccessBitMem_size_ge288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    288 ≤ (setRewardConfigSuccessBitMem I baseOut decOut rescale bit).size := by
  have hrescale := setRewardConfigSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  unfold setRewardConfigSuccessBitMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))

theorem setRewardConfigSuccessMultiplierMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigSuccessMultiplierMem I baseOut decOut rescale bit).size := by
  have hbit := setRewardConfigSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigSuccessMultiplierMem
  rw [writeWord_size]
  · omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))

theorem setRewardConfigSuccessCometMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigSuccessCometMem I baseOut decOut rescale bit).size := by
  unfold setRewardConfigSuccessCometMem
  rw [writeWord_size]
  · have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))

theorem setRewardConfigSuccessArgsMem_size_ge320
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    320 ≤ (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size := by
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_size]
  · have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))

theorem setRewardConfigSuccessArgsMem_read0
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 0 32 =
      UInt256.toByteArray (setRewardConfigWithMultiplierCometWord I) := by
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigSuccessCometMem
    rw [writeWord_read_back]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · left
    have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    constructor <;> omega

theorem setRewardConfigSuccessArgsMem_read32
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 32 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_back]
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))

theorem setRewardConfigSuccessArgsMem_read0_64
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 0 64 =
      UInt256.toByteArray (setRewardConfigWithMultiplierCometWord I) ++
        UInt256.toByteArray (⟨1⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split _ 0 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [setRewardConfigSuccessArgsMem_read0 I rescale bit hdec32 hdecSize,
      setRewardConfigSuccessArgsMem_read32 I rescale bit hdec32 hdecSize]
  · have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    omega

theorem setRewardConfigSuccessArgsMem_keccakSlot
    (I : ExecutionEnv) (baseOut decOut : ByteArray) (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I) := by
  rw [setRewardConfigSuccessArgsMem_read0_64 I baseOut decOut rescale bit hdec32 hdecSize]
  unfold solcMappingSlot
  exact mappingSlot_single (setRewardConfigWithMultiplierCometWord I) ⟨1⟩

theorem setRewardConfigSuccessArgsMem_read64
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold setRewardConfigSuccessArgsMem setRewardConfigSuccessCometMem
  rw [writeWord_read_preserved, writeWord_read_preserved]
  · unfold setRewardConfigSuccessMultiplierMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigSuccessBitMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigSuccessRescaleMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigSuccessTokenMem
          rw [writeWord_read_preserved]
          · unfold setRewardConfigSuccessFreeMem
            rw [writeWord_read_back]
            exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num))
          · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 192 (by norm_num))
          · left
            have hfree := setRewardConfigSuccessFreeMem_size_ge192 I (baseOut := baseOut)
              hdec32 hdecSize
            constructor <;> omega
        · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 224 (by norm_num))
        · left
          have htoken := setRewardConfigSuccessTokenMem_size_ge224 I (baseOut := baseOut)
            hdec32 hdecSize
          constructor <;> omega
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
      · left
        have hrescale := setRewardConfigSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
          rescale hdec32 hdecSize
        constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
    · left
      have hbit := setRewardConfigSuccessBitMem_size_ge288 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
  · right
    have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
      rescale bit hdec32 hdecSize
    constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right
    have hcomet :
        320 ≤ (Reasoning.Theory.writeWord
          (setRewardConfigSuccessMultiplierMem I baseOut decOut rescale bit) 0
          (setRewardConfigWithMultiplierCometWord I)).size := by
      simpa [setRewardConfigSuccessCometMem] using
        setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
          rescale bit hdec32 hdecSize
    constructor <;> omega

theorem setRewardConfigSuccessArgsMem_mload64
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨64⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨320⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := ⟨320⟩)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      exact setRewardConfigSuccessArgsMem_read64 I rescale bit hdec32 hdecSize)

theorem setRewardConfigSuccessArgsMem_read192
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 192 32 =
      UInt256.toByteArray (setRewardConfigDecimalsTargetWord I) := by
  have htoken := setRewardConfigSuccessTokenMem_size_ge224 I (baseOut := baseOut)
    hdec32 hdecSize
  have hrescale := setRewardConfigSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  have hbit := setRewardConfigSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigSuccessBitMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigSuccessRescaleMem
          rw [writeWord_read_preserved]
          · unfold setRewardConfigSuccessTokenMem
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

theorem setRewardConfigSuccessArgsMem_read224
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 224 32 =
      UInt256.toByteArray rescale := by
  have hrescale := setRewardConfigSuccessRescaleMem_size_ge256 I (baseOut := baseOut)
    rescale hdec32 hdecSize
  have hbit := setRewardConfigSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigSuccessBitMem
        rw [writeWord_read_preserved]
        · unfold setRewardConfigSuccessRescaleMem
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

theorem setRewardConfigSuccessArgsMem_read256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 256 32 =
      UInt256.toByteArray bit := by
  have hbit := setRewardConfigSuccessBitMem_size_ge288 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigSuccessMultiplierMem
      rw [writeWord_read_preserved]
      · unfold setRewardConfigSuccessBitMem
        rw [writeWord_read_back]
        exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 256 (by norm_num))
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
      · left; constructor <;> omega
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigSuccessArgsMem_read288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding 288 32 =
      UInt256.toByteArray (setRewardConfigWithMultiplierMultiplierWord I) := by
  have hmul := setRewardConfigSuccessMultiplierMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  have hcomet := setRewardConfigSuccessCometMem_size_ge320 I (baseOut := baseOut)
    rescale bit hdec32 hdecSize
  unfold setRewardConfigSuccessArgsMem
  rw [writeWord_read_preserved]
  · unfold setRewardConfigSuccessCometMem
    rw [writeWord_read_preserved]
    · unfold setRewardConfigSuccessMultiplierMem
      rw [writeWord_read_back]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by norm_num))
    · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 0 (by norm_num))
    · right; constructor <;> omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 32 (by norm_num))
  · right; constructor <;> omega

theorem setRewardConfigSuccessArgsMem_mload192
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨192⟩ : UInt256).toNat ≥
          (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨192⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨192⟩ : UInt256).toNat 32))) =
      setRewardConfigDecimalsTargetWord I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨192⟩ : UInt256)) (aw := (⟨10⟩ : UInt256))
    (v := setRewardConfigDecimalsTargetWord I)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
      exact setRewardConfigSuccessArgsMem_read192 I rescale bit hdec32 hdecSize)

theorem setRewardConfigSuccessArgsMem_mload224
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨224⟩ : UInt256).toNat ≥
          (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨224⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨224⟩ : UInt256).toNat 32))) = rescale := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨224⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := rescale)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
      exact setRewardConfigSuccessArgsMem_read224 I rescale bit hdec32 hdecSize)

theorem setRewardConfigSuccessArgsMem_mload256
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨256⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) = bit := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (aw := (⟨10⟩ : UInt256)) (v := bit)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide]
      exact setRewardConfigSuccessArgsMem_read256 I rescale bit hdec32 hdecSize)

theorem setRewardConfigSuccessArgsMem_mload288
    (I : ExecutionEnv) {baseOut decOut : ByteArray} (rescale bit : UInt256)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).size
        ∨ (⟨288⟩ : UInt256) ≥ (⟨10⟩ : UInt256) * ⟨32⟩ then
      ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setRewardConfigSuccessArgsMem I baseOut decOut rescale bit).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) =
      setRewardConfigWithMultiplierMultiplierWord I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨288⟩ : UInt256)) (aw := (⟨10⟩ : UInt256))
    (v := setRewardConfigWithMultiplierMultiplierWord I)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      have hsize := setRewardConfigSuccessArgsMem_size_ge320 I (baseOut := baseOut)
        rescale bit hdec32 hdecSize
      omega)
    (by native_decide)
    (by
      rw [show (⟨288⟩ : UInt256).toNat = 288 from by decide]
      exact setRewardConfigSuccessArgsMem_read288 I rescale bit hdec32 hdecSize)

private abbrev setRewardConfigAfterDecimalsSafe64BranchPc : UInt256 :=
  ⟨294⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
    ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 +
    ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_safe64_prefix
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
            (UInt256.land (⟨255⟩ : UInt256)
              (setRewardConfigDecimalsReturnWord decOut)))
          (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) =
        tokenScale ∧
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
          (UInt256.land
            (UInt256.exp (⟨10⟩ : UInt256)
              (UInt256.land (⟨255⟩ : UInt256)
                (setRewardConfigDecimalsReturnWord decOut)))
            (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) =
        tokenScale ∧
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        setRewardConfigAfterDecimalsSafe64BranchPc
        [UInt256.gt baseWord tokenScale, baseWord, tokenScale, ⟨32⟩, ⟨1⟩, solcAddrMask,
          setRewardConfigWithMultiplierCometWord I, ⟨224⟩,
          ((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩,
          setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
          setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigDecimalsPostDecodeMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
        decOut acc k' C' := by
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
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd648 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd656 := evm_run rd648 with [
    raw mload 0 decWord setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd656zero := rd656
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd656zero
  have rd302 := evm_run rd656zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨294⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hle77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨0⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_zero
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hle77'
  have rd302le := rd302
  rw [hle77Word] at rd302le
  let tokenScale : UInt256 := UInt256.exp (⟨10⟩ : UInt256) decWord
  have htokenScale_toNat : tokenScale.toNat = (10 : ℕ) ^ decWord.toNat := by
    unfold tokenScale
    rw [← u256_ofNat_toNat decWord]
    interval_cases decWord.toNat <;> native_decide
  have rd320 := evm_run rd302le with [
    push2 ⟨597⟩, jumpiNT (by native_decide), push1 ⟨10⟩, exp,
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, swap7, dup8, dup3, gt]
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
  have rd320le := rd320
  rw [show UInt256.gt (UInt256.exp (⟨10⟩ : UInt256)
        (UInt256.land (⟨255⟩ : UInt256) decWord))
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ by
      rw [hmaskedDec]
      simpa [tokenScale] using hgtToken] at rd320le
  have rd337 := evm_run rd320le with [
    push2 ⟨577⟩, jumpiNT (by native_decide), pop, swap1, dup7, dup10, swap4, swap3,
    and, swap1, dup2, dup9, dup3, and, gt]
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
  have rd337clean := rd337
  rw [hbaseClean, htokenClean] at rd337clean
  obtain ⟨k337, C337, rd337final⟩ : ∃ k337 C337,
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
        setRewardConfigAfterDecimalsSafe64BranchPc
        [UInt256.gt baseWord tokenScale, baseWord, tokenScale, ⟨32⟩, ⟨1⟩, solcAddrMask,
          setRewardConfigWithMultiplierCometWord I, ⟨224⟩,
          ((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩,
          setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
          setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigDecimalsPostDecodeMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
        decOut acc k337 C337 := by
    exact ⟨_, _, by
      simpa [setRewardConfigAfterDecimalsSafe64BranchPc, decWord, tokenScale] using
        rd337clean⟩
  refine ⟨tokenScale, k337, C337, ?_⟩
  refine ⟨?_, hbaseClean, ?_, ?_, rd337final⟩
  · simpa [decWord] using htokenScale_toNat
  · simpa [decWord] using htokenClean
  · simpa [decWord] using htokenCleanLeft

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_noncanon_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd648 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd656 := evm_run rd648 with [
    raw mload 0 decWord setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hnotClean : UInt256.land decWord uint8Mask ≠ decWord :=
    uint8Mask_not_clean hdec8'
  have hneq : decWord ≠ UInt256.land decWord uint8Mask := by
    intro hEq
    exact hnotClean hEq.symm
  have hsub : UInt256.sub decWord (UInt256.land decWord uint8Mask) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hneq
  have rd667 := evm_run rd656 with [
    push2 ⟨667⟩, jumpiT (by simpa [uint8Mask] using hsub) (by jump_dest)]
  exact evm_run rd667 with [jumpdest, dup1, raw rev 0 (by native_decide) mem_cost
    (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_pow10_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd648 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd656 := evm_run rd648 with [
    raw mload 0 decWord setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd656zero := rd656
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd656zero
  have rd302 := evm_run rd656zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨294⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hgt77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨1⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_one
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hgt77'
  have rd302gt := rd302
  rw [hgt77Word] at rd302gt
  have rd597 := evm_run rd302gt with [
    push2 ⟨597⟩, jumpiT (by native_decide) (by jump_dest)]
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        setRewardConfigPanicSelector := by
    rfl
  have rd611₀ := evm_run rd597 with [
    jumpdest, push1 ⟨17⟩, dup8, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl,
    push1 ⟨0⟩]
  have rd611 := rd611₀
  rw [hsel] at rd611
  have rd612 := evm_run rd611 with [
    raw mstore 0 (setRewardConfigPanicMem0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd613 := evm_run rd612 with [
    raw mstore 0
      (setRewardConfigPanicMem ⟨17⟩ (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd613 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 3000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_safe64_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd648 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd656 := evm_run rd648 with [
    raw mload 0 decWord setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd656zero := rd656
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd656zero
  have rd302 := evm_run rd656zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨294⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hle77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨0⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_zero
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hle77'
  have rd302le := rd302
  rw [hle77Word] at rd302le
  let tokenScale : UInt256 := UInt256.exp (⟨10⟩ : UInt256) decWord
  have hpowBound : (10 : ℕ) ^ decWord.toNat < UInt256.size := by
    have hpowLe : (10 : ℕ) ^ decWord.toNat ≤ 10 ^ 77 :=
      Nat.pow_le_pow_right (by norm_num) hle77'
    exact lt_of_le_of_lt hpowLe (by norm_num [UInt256.size])
  have htokenScale_toNat : tokenScale.toNat = (10 : ℕ) ^ decWord.toNat := by
    unfold tokenScale
    rw [← u256_ofNat_toNat decWord]
    interval_cases decWord.toNat <;> native_decide
  have rd320 := evm_run rd302le with [
    push2 ⟨597⟩, jumpiNT (by native_decide), push1 ⟨10⟩, exp,
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, swap7, dup8, dup3, gt]
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
  have rd320gt := rd320
  rw [show UInt256.gt (UInt256.exp (⟨10⟩ : UInt256)
        (UInt256.land (⟨255⟩ : UInt256) decWord))
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨1⟩ by
      rw [hmaskedDec]
      simpa [tokenScale] using hgtToken] at rd320gt
  have rd577 := evm_run rd320gt with [
    push2 ⟨577⟩, jumpiT (by native_decide) (by jump_dest)]
  have hsel :
      UInt256.shiftLeft (⟨0x4809a3⟩ : UInt256) ⟨226⟩ =
        setRewardConfigInvalidUInt64Selector := by
    rfl
  have rd582 := evm_run rd577 with [
    jumpdest, push1 ⟨36⟩, swap2, dup13]
  have rd583 := evm_run rd582 with [
    raw mload 0 ⟨192⟩ setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (setRewardConfigDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rd584 := evm_run rd583 with [
    swap2]
  have rd588 := rd584.pushConst (⟨0x4809a3⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd592₀ := evm_run rd588 with [
    push1 ⟨226⟩, shl, dup4]
  have rd592 := rd592₀
  rw [hsel] at rd592
  let awInvalidSelector : UInt256 :=
    UInt256.ofNat (MachineState.M setRewardConfigDecimalsPostCallAw.toNat
      (⟨192⟩ : UInt256).toNat 32)
  let awInvalidArg : UInt256 :=
    UInt256.ofNat (MachineState.M awInvalidSelector.toNat
      ((⟨192⟩ : UInt256) + ⟨4⟩).toNat 32)
  have rd593 := evm_run rd592 with [
    raw mstore (Cₘ awInvalidSelector - Cₘ setRewardConfigDecimalsPostCallAw)
      (setRewardConfigInvalidUInt64SelectorMem
        (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      awInvalidSelector (by native_decide) mem_cost
      (by unfold setRewardConfigInvalidUInt64SelectorMem; rfl)
      (by rfl) (by evm_ov)]
  have rd596 := evm_run rd593 with [
    dup3, add,
    raw mstore (Cₘ awInvalidArg - Cₘ awInvalidSelector)
      (setRewardConfigInvalidUInt64Mem tokenScale
        (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      awInvalidArg (by native_decide) mem_cost
      (by
        unfold setRewardConfigInvalidUInt64Mem setRewardConfigInvalidUInt64SelectorMem tokenScale
        rw [hmaskedDec]
        rw [show ((⟨192⟩ : UInt256) + ⟨4⟩).toNat = 196 from by native_decide])
      (by rfl) (by evm_ov)]
  exact evm_run rd596 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_short_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
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
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, pop, returndatasize, push2 ⟨629⟩, jump (by jump_dest),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩,
    jumpiNT (by simpa [ptr, rounded] using hallocOk), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostShortDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by native_decide) (by evm_ov)]
  have rd639 := evm_run rd3105 with [
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
  have rd644₀ := evm_run rd639 with [
    dup2, add, sub, slt]
  have rd644 := rd644₀
  rw [hlenCheck] at rd644
  have rd670 := evm_run rd644 with [
    push2 ⟨670⟩, jumpiT (by native_decide) (by jump_dest)]
  exact evm_run rd670 with [jumpdest, pop, dup1, raw rev 0 (by native_decide) mem_cost
    (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_downscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
    (hperm : I.perm = true)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
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
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigWithMultiplierSlotOf I)
            (setRewardConfigSlot0Down
              (solcSlotWord acc.2 I (setRewardConfigWithMultiplierSlotOf I))
              (setRewardConfigWithMultiplierTokenWord I) rescale))
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I))
      ByteArray.empty := by
  let decWord : UInt256 := setRewardConfigDecimalsReturnWord decOut
  have hdec8' : decWord.toNat < EVM.twoPow 8 := by
    simpa [decWord] using hdec8
  have hle77' : decWord.toNat ≤ 77 := by
    simpa [decWord] using hle77
  have hsafe64' : (10 : ℕ) ^ decWord.toNat ≤ 2 ^ 64 - 1 := by
    simpa [decWord] using hsafe64
  have hdown' : (10 : ℕ) ^ decWord.toNat < baseWord.toNat := by
    simpa [decWord] using hdown
  have hrescale' : rescale.toNat = baseWord.toNat / (10 : ℕ) ^ decWord.toNat := by
    simpa [decWord] using hrescale
  let rdsz : UInt256 := UInt256.ofNat decOut.size
  have hrdsz_toNat : rdsz.toNat = decOut.size := by
    simpa [rdsz] using UInt256.toNat_ofNat_of_lt hdecSize
  have hgt : UInt256.gt (⟨32⟩ : UInt256) rdsz = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, hrdsz_toNat]
    exact hdec32
  have rd280 : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨280⟩
      [⟨1⟩, ⟨160⟩, baseWord, ⟨32⟩, solcAddrMask,
        setRewardConfigWithMultiplierCometWord I, ⟨224⟩, ⟨4⟩,
        setRewardConfigWithMultiplierMultiplierWord I, ⟨1⟩,
        setRewardConfigDecimalsTargetWord I, ⟨64⟩, ⟨0⟩]
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C := by
    simpa [setRewardConfigDecimalsPostCallStack, setRewardConfigDecimalsPostCallTail] using rd
  have rd625₀ := evm_run rd280 with [
    swap1, dup2, iszero, push2 ⟨681⟩, jumpiNT (by native_decide),
    push1 ⟨0⟩, swap2, push2 ⟨618⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest, dup4, dup2, dup2, returndatasize, dup4, gt]
  have rd625 := rd625₀
  rw [show UInt256.ofNat decOut.size = rdsz from rfl, hgt] at rd625
  have rd3071 := evm_run rd625 with [
    push2 ⟨674⟩, jumpiNT (by native_decide),
    jumpdest, push2 ⟨639⟩, dup2, dup4, push2 ⟨3071⟩, jump (by jump_dest),
    jumpdest, push1 ⟨31⟩, swap1, swap2, add, push1 ⟨31⟩, not, and, dup2,
    add, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt,
    swap1, dup3, lt, lor, push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩]
  have rd3105 := evm_run rd3071 with [
    raw mstore 0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        unfold setRewardConfigDecimalsPostDecodeMem
        rfl)
      (by native_decide) (by evm_ov)]
  have rd648 := evm_run rd3105 with [
    jump (by jump_dest), jumpdest, dup2, add, sub, slt,
    push2 ⟨670⟩, jumpiNT (by native_decide)]
  have rd656 := evm_run rd648 with [
    raw mload 0 decWord setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (by
        simpa [decWord, setRewardConfigDecimalsReturnWord] using
          setRewardConfigDecimalsPostDecodeMem_mload160_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap1, push1 ⟨255⟩, dup3, and, dup3, sub]
  have hclean : UInt256.land decWord uint8Mask = decWord :=
    uint8Mask_clean hdec8'
  have hsubZero :
      UInt256.sub decWord (UInt256.land decWord uint8Mask) = ⟨0⟩ := by
    rw [hclean]
    exact u256_sub_self decWord
  have rd656zero := rd656
  rw [show UInt256.sub decWord (UInt256.land decWord ⟨255⟩) = ⟨0⟩ by
      simpa [uint8Mask] using hsubZero] at rd656zero
  have rd302 := evm_run rd656zero with [
    push2 ⟨667⟩, jumpiNT (by native_decide), pop, push1 ⟨255⟩,
    push2 ⟨294⟩, jump (by jump_dest), jumpdest, pop, push1 ⟨255⟩, and,
    push1 ⟨77⟩, dup2, gt]
  have hle77Word :
      UInt256.gt (UInt256.land (⟨255⟩ : UInt256) decWord) (⟨77⟩ : UInt256) = ⟨0⟩ := by
    rw [u256_land_comm (⟨255⟩ : UInt256) decWord]
    rw [show UInt256.land decWord ⟨255⟩ = decWord by simpa [uint8Mask] using hclean]
    apply ugt_zero
    rw [show (⟨77⟩ : UInt256).toNat = 77 from by decide]
    exact hle77'
  have rd302le := rd302
  rw [hle77Word] at rd302le
  let tokenScale : UInt256 := UInt256.exp (⟨10⟩ : UInt256) decWord
  have htokenScale_toNat : tokenScale.toNat = (10 : ℕ) ^ decWord.toNat := by
    unfold tokenScale
    rw [← u256_ofNat_toNat decWord]
    interval_cases decWord.toNat <;> native_decide
  have rd320 := evm_run rd302le with [
    push2 ⟨597⟩, jumpiNT (by native_decide), push1 ⟨10⟩, exp,
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, swap7, dup8, dup3, gt]
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
  have rd320le := rd320
  rw [show UInt256.gt (UInt256.exp (⟨10⟩ : UInt256)
        (UInt256.land (⟨255⟩ : UInt256) decWord))
      (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = ⟨0⟩ by
      rw [hmaskedDec]
      simpa [tokenScale] using hgtToken] at rd320le
  have rd337 := evm_run rd320le with [
    push2 ⟨577⟩, jumpiNT (by native_decide), pop, swap1, dup7, dup10, swap4, swap3,
    and, swap1, dup2, dup9, dup3, and, gt]
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
  have hdownWord :
      UInt256.gt
        (UInt256.land baseWord (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩))
        (UInt256.land
          (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord))
          (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)) = ⟨1⟩ := by
    rw [hbaseClean, htokenClean]
    apply ugt_one
    rw [htokenScale_toNat]
    exact hdown'
  have htokenNZ : tokenScale ≠ ⟨0⟩ := by
    intro hzero
    have hto := congrArg UInt256.toNat hzero
    rw [htokenScale_toNat, show (⟨0⟩ : UInt256).toNat = 0 from rfl] at hto
    have hpos : 0 < (10 : ℕ) ^ decWord.toNat := by positivity
    omega
  have hrescaleWord :
      UInt256.div baseWord tokenScale = rescale := by
    apply u256_inj
    rw [udiv_toNat, htokenScale_toNat, hrescale']
  have hrescale64 : rescale.toNat < EVM.twoPow 64 := by
    rw [hrescale']
    have hdiv := Nat.div_le_self baseWord.toNat ((10 : ℕ) ^ decWord.toNat)
    have hbase64' : baseWord.toNat < 2 ^ 64 := by
      simpa [EVM.twoPow] using hbase64
    simpa [EVM.twoPow] using lt_of_le_of_lt hdiv hbase64'
  have hrescaleClean :
      UInt256.land rescale (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩) = rescale := by
    simpa [uint64Mask] using uint64Mask_clean hrescale64
  have rd337down := rd337
  rw [hdownWord] at rd337down
  have rd354 := evm_run rd337down with [
    push1 ⟨0⟩, eq, push2 ⟨466⟩, jumpiNT (by native_decide),
    swap1, push2 ⟨354⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap2, dup3, and,
    swap2, swap1, dup3, iszero]
  rw [show UInt256.isZero
      (UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩)
        (UInt256.land
          (UInt256.exp (⟨10⟩ : UInt256) (UInt256.land (⟨255⟩ : UInt256) decWord))
          (((⟨1⟩ : UInt256).shiftLeft ⟨64⟩).sub ⟨1⟩))) = ⟨0⟩ by
      rw [htokenCleanLeft]
      exact isZero_eq_zero_of_ne htokenNZ] at rd354
  have rd354ret := evm_run rd354 with [
    push2 ⟨3161⟩, jumpiNT (by native_decide), and, div, swap1, jump (by jump_dest),
    jumpdest]
  rw [hbaseClean, htokenCleanLeft, hrescaleWord] at rd354ret
  have rd354rescale := rd354ret
  have rd367pre := evm_run rd354rescale with [
    swap6, dup11,
    raw mload 0 ⟨192⟩ setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap10, push2 ⟨367⟩]
  have rd367arg := rdDup12 rd367pre (by native_decide) (by simp)
  have rd367 := evm_run rd367arg with [
    push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (setRewardConfigSuccessFreeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessFreeMem Reasoning.Theory.writeWord; rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
  have rd369 := evm_run rd367 with [
    dup11,
    raw mstore 3 (setRewardConfigSuccessTokenMem I baseOut decOut)
      (⟨7⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessTokenMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd372 := evm_run rd369 with [swap1, swap6, and]
  rw [hrescaleClean] at rd372
  have rd378 := evm_run rd372 with [
    dup6, dup10, add, swap1, dup2,
    raw mstore 3 (setRewardConfigSuccessRescaleMem I baseOut decOut rescale)
      (⟨8⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessRescaleMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd386 := evm_run rd378 with [
    push1 ⟨0⟩, dup11, dup11, add, dup2, dup2,
    raw mstore 3 (setRewardConfigSuccessBitMem I baseOut decOut rescale ⟨0⟩)
      (⟨9⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessBitMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd389pre := evm_run rd386 with [push1 ⟨96⟩]
  have rd390arg := rdDup12 rd389pre (by native_decide) (by simp)
  have rd391 := evm_run rd390arg with [add]
  have rd392 := rdSwap9 rd391 (by native_decide) (by simp)
  have rd393 := evm_run rd392 with [
    dup10,
    raw mstore 3 (setRewardConfigSuccessMultiplierMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessMultiplierMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd397 := evm_run rd393 with [
    swap5, dup2,
    raw mstore 0 (setRewardConfigSuccessCometMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessCometMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd401 := evm_run rd397 with [
    swap2, swap1, swap6,
    raw mstore 0 (setRewardConfigSuccessArgsMem I baseOut decOut rescale ⟨0⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessArgsMem; rfl)
      (by native_decide) (by evm_ov)]
  have hslot := setRewardConfigWithMultiplierSlotOf_eq_solc I hcanon0
  have hkeccak :=
    setRewardConfigSuccessArgsMem_keccakSlot I baseOut decOut rescale ⟨0⟩ hdec32 hdecSize
  have rd404pre := evm_run rd401 with [dup9, swap1]
  have rd404₀ := rd404pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I))
    (⟨10⟩ : UInt256) (by native_decide) mem_cost hkeccak (by native_decide) (by evm_ov)
  have rd404 := rd404₀
  rw [← hslot] at rd404
  have rd406 := evm_run rd404 with [
    swap7,
    raw mload 0 (setRewardConfigDecimalsTargetWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload192 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    dup8]
  obtain ⟨_, _, rd408⟩ := rd406.sload (by native_decide) (by evm_ov)
  have rd412 := evm_run rd408 with [
    swap5,
    raw mload 0 rescale (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload224 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap3,
    raw mload 0 (⟨0⟩ : UInt256) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload256 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rd459 := evm_run rd412 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨232⟩, shl, sub, not, swap1, swap6, and,
    swap2, and, lor, push1 ⟨160⟩, swap2, swap1, swap2, shl,
    push1 ⟨1⟩, push1 ⟨160⟩, shl, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub, and, lor,
    swap2, iszero, iszero, swap1, shl, push1 ⟨255⟩, push1 ⟨224⟩, shl, and, lor,
    dup4]
  let oldSlot : UInt256 := solcSlotWord acc.2 I (setRewardConfigWithMultiplierSlotOf I)
  have rd459packed := rd459
  rw [show
      ((UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩).land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256))) ⟨224⟩)).lor
        ((((UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
                (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩)).land
              (UInt256.shiftLeft rescale ⟨160⟩)).lor
          ((UInt256.land solcAddrMask (setRewardConfigDecimalsTargetWord I)).lor
            (UInt256.land oldSlot
              (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩)
                ⟨1⟩)))))) =
        setRewardConfigSlot0Down oldSlot (setRewardConfigDecimalsTargetWord I) rescale by
        exact setRewardConfigSlot0Down_bytecodeExpr oldSlot
          (setRewardConfigDecimalsTargetWord I) rescale] at rd459packed
  obtain ⟨_, _, rd459fold⟩ : ∃ k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨459⟩
        [setRewardConfigWithMultiplierSlotOf I,
          setRewardConfigSlot0Down oldSlot (setRewardConfigDecimalsTargetWord I) rescale,
          ⟨192⟩ + ⟨96⟩, ⟨1⟩, setRewardConfigWithMultiplierSlotOf I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigSuccessArgsMem I baseOut decOut rescale ⟨0⟩) (⟨10⟩ : UInt256)
        decOut (acc.1, acc.2) k' C' := by
    exact ⟨_, _, by simpa [oldSlot, solcSlotWord] using rd459packed⟩
  have htargetWord :
      setRewardConfigDecimalsTargetWord I = setRewardConfigWithMultiplierTokenWord I := by
    unfold setRewardConfigDecimalsTargetWord
    rw [u256_land_comm solcAddrMask (setRewardConfigWithMultiplierTokenWord I)]
    exact solcAddrMask_clean hcanon1
  rw [htargetWord] at rd459fold
  obtain ⟨_, _, rd460⟩ := rd459fold.sstore hperm (by native_decide) (by evm_ov)
  have rd463pre := evm_run rd460 with [
    raw mload 0 (setRewardConfigWithMultiplierMultiplierWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload288 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap2, add]
  obtain ⟨_, _, rd464⟩ := rd463pre.sstore hperm (by native_decide) (by evm_ov)
  have rd465 := evm_run rd464 with [
    raw mload 0 ⟨320⟩ (⟨10⟩ : UInt256) (by native_decide)
      mem_cost
      (setRewardConfigSuccessArgsMem_mload64 I rescale ⟨0⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rdret : RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigWithMultiplierSlotOf I)
            (setRewardConfigSlot0Down oldSlot (setRewardConfigWithMultiplierTokenWord I)
              rescale))
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I))
      ByteArray.empty := by
    exact RD.ret 0 ByteArray.empty rd465 (by native_decide)
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
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_upscale_zero_revert
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
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
      _htokenCleanLeft, rd337⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_after_decimals_safe64_prefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (baseOut := baseOut) (decOut := decOut)
      (baseWord := baseWord) (acc := acc) (k := k) (C := C)
      rd hdec32 hdecSize hdec8 hle77 hsafe64 hbase64
  have hupWord : UInt256.gt baseWord tokenScale = ⟨0⟩ := by
    apply ugt_zero
    rw [htokenScale_toNat]
    exact hle
  have rd337up := rd337
  rw [hupWord] at rd337up
  have rd466 := evm_run rd337up with [
    push1 ⟨0⟩, eq, push2 ⟨466⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest]
  have rd3137 := evm_run rd466 with [
    push2 ⟨475⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest)]
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
    raw mstore 0 (setRewardConfigPanicMem0 (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov)]
  have rd3178 := evm_run rd3173 with [
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0
      (setRewardConfigPanicMem ⟨18⟩ (setRewardConfigDecimalsPostDecodeMem I baseOut decOut))
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigPanicMem setRewardConfigPanicMem0; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, push1 ⟨0⟩]
  exact evm_run rd3178 with [raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsSetRewardConfigWithMultiplierX_after_decimals_upscale_success
    {cA gh bl σ σ₀ A I} {g : Sat256} {baseOut decOut : ByteArray}
    {baseWord rescale : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd : RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      (setRewardConfigDecimalsPostCallStack true baseWord I)
      (setRewardConfigDecimalsPostCallMem I baseOut decOut) setRewardConfigDecimalsPostCallAw
      decOut acc k C)
    (hdec32 : 32 ≤ decOut.size) (hdecSize : decOut.size < UInt256.size)
    (hdec8 : (setRewardConfigDecimalsReturnWord decOut).toNat < EVM.twoPow 8)
    (hle77 : (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 77)
    (hsafe64 : (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat ≤ 2 ^ 64 - 1)
    (hbase64 : baseWord.toNat < EVM.twoPow 64)
    (hperm : I.perm = true)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hle : baseWord.toNat ≤
      (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat)
    (hbaseNZ : baseWord.toNat ≠ 0)
    (hrescale : rescale.toNat =
      (10 : ℕ) ^ (setRewardConfigDecimalsReturnWord decOut).toNat / baseWord.toNat) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigWithMultiplierSlotOf I)
            (setRewardConfigSlot0Up
              (solcSlotWord acc.2 I (setRewardConfigWithMultiplierSlotOf I))
              (setRewardConfigWithMultiplierTokenWord I) rescale))
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I))
      ByteArray.empty := by
  obtain ⟨tokenScale, _, _, htokenScale_toNat, hbaseClean, _htokenClean,
      _htokenCleanLeft, rd337⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_after_decimals_safe64_prefix
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (baseOut := baseOut) (decOut := decOut)
      (baseWord := baseWord) (acc := acc) (k := k) (C := C)
      rd hdec32 hdecSize hdec8 hle77 hsafe64 hbase64
  have hupWord : UInt256.gt baseWord tokenScale = ⟨0⟩ := by
    apply ugt_zero
    rw [htokenScale_toNat]
    exact hle
  have rd337up := rd337
  rw [hupWord] at rd337up
  have rd466 := evm_run rd337up with [
    push1 ⟨0⟩, eq, push2 ⟨466⟩, jumpiT (by native_decide) (by jump_dest),
    jumpdest]
  have rd3137 := evm_run rd466 with [
    push2 ⟨475⟩, swap2, push2 ⟨3137⟩, jump (by jump_dest)]
  have rd3156pre := evm_run rd3137 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, swap2, dup3, and,
    swap2, swap1, dup3, iszero]
  have hbaseNZWord : UInt256.isZero
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
  have rd475 := evm_run rd3156 with [
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
  have rd475rescale := rd475
  rw [htokenCleanRight, hbaseCleanLeft, hrescaleWord] at rd475rescale
  have rd488pre := evm_run rd475rescale with [
    swap6, dup11,
    raw mload 0 ⟨192⟩ setRewardConfigDecimalsPostCallAw (by native_decide)
      mem_cost
      (setRewardConfigDecimalsPostDecodeMem_mload64_of_size_ge I hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap10, push2 ⟨488⟩]
  have rd488arg := rdDup12 rd488pre (by native_decide) (by simp)
  have rd488 := evm_run rd488arg with [
    push2 ⟨3025⟩, jump (by jump_dest),
    jumpdest, push1 ⟨128⟩, dup2, add, swap1, dup2, lt,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨64⟩, shl, sub, dup3, gt, lor,
    push2 ⟨3003⟩, jumpiNT (by native_decide), push1 ⟨64⟩,
    raw mstore 0 (setRewardConfigSuccessFreeMem I baseOut decOut)
      setRewardConfigDecimalsPostCallAw (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessFreeMem Reasoning.Theory.writeWord; rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest), jumpdest]
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
  have rd490 := evm_run rd488 with [
    dup11,
    raw mstore 3 (setRewardConfigSuccessTokenMem I baseOut decOut)
      (⟨7⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessTokenMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd495pre := evm_run rd490 with [
    dup2, dup11, add, swap7, and]
  have rd495 := rd495pre
  rw [hrescaleClean] at rd495
  have rd497 := evm_run rd495 with [
    dup7,
    raw mstore 3 (setRewardConfigSuccessRescaleMem I baseOut decOut rescale)
      (⟨8⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessRescaleMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd504 := evm_run rd497 with [
    dup10, dup10, add, swap4, dup3, dup6,
    raw mstore 3 (setRewardConfigSuccessBitMem I baseOut decOut rescale ⟨1⟩)
      (⟨9⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessBitMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd511 := evm_run rd504 with [
    push1 ⟨96⟩, dup11, add, swap8, dup9,
    raw mstore 3 (setRewardConfigSuccessMultiplierMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessMultiplierMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd514 := evm_run rd511 with [
    push1 ⟨0⟩,
    raw mstore 0 (setRewardConfigSuccessCometMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessCometMem; rfl)
      (by native_decide) (by evm_ov)]
  have rd515 := evm_run rd514 with [
    raw mstore 0 (setRewardConfigSuccessArgsMem I baseOut decOut rescale ⟨1⟩)
      (⟨10⟩ : UInt256) (by native_decide) mem_cost
      (by unfold setRewardConfigSuccessArgsMem; rfl)
      (by native_decide) (by evm_ov)]
  have hslot := setRewardConfigWithMultiplierSlotOf_eq_solc I hcanon0
  have hkeccak :=
    setRewardConfigSuccessArgsMem_keccakSlot I baseOut decOut rescale ⟨1⟩ hdec32 hdecSize
  have rd519pre := evm_run rd515 with [dup8, push1 ⟨0⟩]
  have rd519₀ := rd519pre.keccak256 0
    (solcMappingSlot ⟨1⟩ (setRewardConfigWithMultiplierCometWord I))
    (⟨10⟩ : UInt256) (by native_decide) mem_cost hkeccak (by native_decide) (by evm_ov)
  have rd519 := rd519₀
  rw [← hslot] at rd519
  have rd524 := evm_run rd519 with [
    swap7,
    raw mload 0 (setRewardConfigDecimalsTargetWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload192 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    and, swap1, dup7]
  obtain ⟨_, _, rd525⟩ := rd524.sload (by native_decide) (by evm_ov)
  have rd557 := evm_run rd525 with [
    swap4, push1 ⟨1⟩, push1 ⟨160⟩, shl, push1 ⟨1⟩, push1 ⟨224⟩, shl, sub,
    swap1,
    raw mload 0 rescale (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload224 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    push1 ⟨160⟩, shl, and, swap3, push1 ⟨255⟩, push1 ⟨224⟩, shl, swap2,
    raw mload 0 (⟨1⟩ : UInt256) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload256 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    iszero, iszero, swap1, shl, and, swap3]
  have rd562 := rd557.pushConst (⟨0xffffff⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd569 := evm_run rd562 with [
    push1 ⟨232⟩, shl, and, lor, lor, lor, dup4]
  let oldSlot : UInt256 := solcSlotWord acc.2 I (setRewardConfigWithMultiplierSlotOf I)
  have rd569packed := rd569
  rw [show
      UInt256.lor
        (UInt256.lor
          (UInt256.lor
            (UInt256.land (UInt256.shiftLeft (⟨0xffffff⟩ : UInt256) ⟨232⟩) oldSlot)
            (UInt256.land (setRewardConfigDecimalsTargetWord I) solcAddrMask))
          (UInt256.land (UInt256.shiftLeft rescale ⟨160⟩)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩))))
        (UInt256.land
          (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) ⟨224⟩)
          (UInt256.shiftLeft (⟨255⟩ : UInt256) ⟨224⟩)) =
        setRewardConfigSlot0Up oldSlot (setRewardConfigDecimalsTargetWord I) rescale by
        exact setRewardConfigSlot0Up_bytecodeExpr_runtime oldSlot
          (setRewardConfigDecimalsTargetWord I) rescale] at rd569packed
  obtain ⟨_, _, rd569fold⟩ : ∃ k' C',
      RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨570⟩
        [setRewardConfigWithMultiplierSlotOf I,
          setRewardConfigSlot0Up oldSlot (setRewardConfigDecimalsTargetWord I) rescale,
          ⟨192⟩ + ⟨96⟩, ⟨1⟩, setRewardConfigWithMultiplierSlotOf I, ⟨64⟩, ⟨0⟩]
        (setRewardConfigSuccessArgsMem I baseOut decOut rescale ⟨1⟩) (⟨10⟩ : UInt256)
        decOut (acc.1, acc.2) k' C' := by
    exact ⟨_, _, by simpa [oldSlot, solcSlotWord] using rd569packed⟩
  have htargetWord :
      setRewardConfigDecimalsTargetWord I = setRewardConfigWithMultiplierTokenWord I := by
    unfold setRewardConfigDecimalsTargetWord
    rw [u256_land_comm solcAddrMask (setRewardConfigWithMultiplierTokenWord I)]
    exact solcAddrMask_clean hcanon1
  rw [htargetWord] at rd569fold
  obtain ⟨_, _, rd570⟩ := rd569fold.sstore hperm (by native_decide) (by evm_ov)
  have rd573pre := evm_run rd570 with [
    raw mload 0 (setRewardConfigWithMultiplierMultiplierWord I) (⟨10⟩ : UInt256)
      (by native_decide) mem_cost
      (setRewardConfigSuccessArgsMem_mload288 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov),
    swap2, add]
  obtain ⟨_, _, rd574⟩ := rd573pre.sstore hperm (by native_decide) (by evm_ov)
  have rd575 := evm_run rd574 with [
    raw mload 0 ⟨320⟩ (⟨10⟩ : UInt256) (by native_decide)
      mem_cost
      (setRewardConfigSuccessArgsMem_mload64 I rescale ⟨1⟩ hdec32 hdecSize)
      (by native_decide) (by evm_ov)]
  have rdret : RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I)
      (acc.1,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner acc.2 (setRewardConfigWithMultiplierSlotOf I)
            (setRewardConfigSlot0Up oldSlot (setRewardConfigWithMultiplierTokenWord I)
              rescale))
          (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
          (setRewardConfigWithMultiplierMultiplierWord I))
      ByteArray.empty := by
    exact RD.ret 0 ByteArray.empty rd575 (by native_decide)
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
theorem cometRewardsSetRewardConfigWithMultiplierX_baseAccrualScale_callDepthLimit
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon0 : (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus)
    (hcanon1 : (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus)
    (hauth : governorReturnWord σ I = solcSourceWord I)
    (htoken : UInt256.land
      (solcSlotWord σ I (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      setRewardConfigWithMultiplierPc (dispatchArmLastStack I) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    RDrev cometRewardsBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨gasArg, k0, C0, rd241⟩ :=
    cometRewardsSetRewardConfigWithMultiplierX_call_baseAccrualScale
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hwv hsz100 hsize hhi hcanon0 hcanon1 hauth htoken hreach
  have rd241Call :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨241⟩
        (gasArg :: setRewardConfigWithMultiplierCometWord I :: ⟨128⟩ :: ⟨4⟩ ::
          ⟨128⟩ :: ⟨32⟩ :: setRewardConfigBasePostCallTail I)
        (setRewardConfigBaseAccrualScaleCalldataMem I)
        (UInt256.ofNat 5) ByteArray.empty (cA, σ) k0 C0 := by
    simpa [setRewardConfigBasePostCallTail] using rd241
  have hdecCall :
      decode cometRewardsBytecode (⟨241⟩ : UInt256) = some (.STATICCALL, .none) := by
    native_decide
  have hdepthInit :
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth = 1024 := by
    simpa [initState] using hdepth
  obtain ⟨k', C', rdPost₀⟩ :=
    RD.uniswapStaticcallDepthLimit (t := setRewardConfigBasePostCallTail I)
      rd241Call hdecCall hdepthInit (by simp [setRewardConfigBasePostCallTail])
  have rdPost :
      RD cometRewardsBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        ⟨242⟩ (setRewardConfigBasePostCallStack false I)
        (setRewardConfigBasePostCallMem I ByteArray.empty) setRewardConfigBasePostCallAw
        ByteArray.empty (cA, σ) k' C' := by
    simpa [setRewardConfigBasePostCallStack, setRewardConfigBasePostCallTail,
      setRewardConfigBasePostCallMem, setRewardConfigBasePostCallAw] using rdPost₀
  exact cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_failure rdPost
    (by simp [UInt256.size])

/-- `setRewardConfigWithMultiplier(address,address,uint256)` body, reached at pc 159. -/
theorem cometRewardsSetRewardConfigWithMultiplierBodyCore {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 10))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      setRewardConfigWithMultiplierPc (dispatchArmLastStack I) solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsSetRewardConfigWithMultiplierSelector_size hsel
  have hd := cometRewardsDispatch_setRewardConfigWithMultiplier (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon0 :
        (setRewardConfigWithMultiplierCometWord I).toNat < EVM.addressModulus
      · by_cases hcanon1 :
          (setRewardConfigWithMultiplierTokenWord I).toNat < EVM.addressModulus
        · have hdec :=
            cometRewardsDecode_setRewardConfigWithMultiplier_ok
              (I := I) hsz100 hhi hcanon0 hcanon1
          have hgovWord : governorWord σ_evm I = governorWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
          have hgovRet :
              governorReturnWord σ_evm I = governorReturnWord σ_solm I := by
            simp [governorReturnWord, hgovWord]
          have hslotWord :
              solcSlotWord σ_evm I (setRewardConfigWithMultiplierSlotOf I) =
                solcSlotWord σ_solm I (setRewardConfigWithMultiplierSlotOf I) :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (setRewardConfigWithMultiplierSlotOf I) ⟨0⟩
          by_cases hauth : governorReturnWord σ_evm I = solcSourceWord I
          · have hauthSolm : governorReturnWord σ_solm I = solcSourceWord I := by
              rw [← hgovRet]
              exact hauth
            have hgovSolm :
                UInt256.land (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨0⟩) solcAddrMask =
                  solcSourceWord
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv := by
              simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                State.lookupAccount] using hauthSolm
            by_cases hconfigured :
                UInt256.land
                  (solcSlotWord σ_evm I (setRewardConfigWithMultiplierSlotOf I))
                  solcAddrMask ≠ ⟨0⟩
            · have hconfiguredSolm :
                  UInt256.land (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask ≠ ⟨0⟩ := by
                simpa [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                  hslotWord] using hconfigured
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (setRewardConfigWithMultiplierStore I)
                    setRewardConfigWithMultiplierTransition.body .reverted := by
                exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_configured
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                  (by simp only [initState]; exact hwv)
                  (by simp only [initState]; exact hhi)
                  hgovSolm
                  hconfiguredSolm
              exact (cometRewardsSetRewardConfigWithMultiplierX_revert_configured
                  (g := Sat256.ofUInt256 g)
                  hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hconfigured hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
            · have htokenZero :
                  UInt256.land
                    (solcSlotWord σ_evm I (setRewardConfigWithMultiplierSlotOf I))
                    solcAddrMask = ⟨0⟩ := by
                exact Classical.not_not.mp hconfigured
              have htokenZeroSolm :
                  UInt256.land (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    (setRewardConfigWithMultiplierSlotOf I)) solcAddrMask = ⟨0⟩ := by
                simpa [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
                  hslotWord] using htokenZero
              by_cases hdepth : I.depth.val < 1024
              · obtain ⟨cA', σ'_evm, σ'_solm, A'_solm, z, out, kPost, CPost,
                    hcallS, hPostAccounts, rdPost, houtSign⟩ :=
                  cometRewardsSetRewardConfigWithMultiplierX_call_baseAccrualScale_made
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hsz100 hsize hhi hcanon0 hcanon1 hauth htokenZero hdepth
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
                        (setRewardConfigWithMultiplierStore I)
                        setRewardConfigWithMultiplierTransition.body .reverted := by
                    exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseCallFailure
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      evmPost I
                      (by simp only [initState]; exact hwv)
                      (by simp only [initState]; exact hhi)
                      hgovSolm
                      htokenZeroSolm
                      (by simpa [evmPost] using hcallS)
                  exact
                    (cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_failure
                        rdPost houtSize)
                      |>.reEquivExecutionRevert hcode hd hdec hbody
                · by_cases hshort : out.size < 32
                  · have hdecBase := cometRewardsBaseAccrualScale_decode_none_short
                      (out := out) hshort
                    have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (setRewardConfigWithMultiplierStore I)
                          setRewardConfigWithMultiplierTransition.body .reverted := by
                      exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseDecodeFailure
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        evmPost I
                        (by simp only [initState]; exact hwv)
                        (by simp only [initState]; exact hhi)
                        hgovSolm
                        htokenZeroSolm
                        (by simpa [evmPost] using hcallS)
                        hdecBase
                    exact
                      (cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_short_revert
                          rdPost hshort houtSize)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
                  · have hout32 : 32 ≤ out.size := by omega
                    by_cases hbaseWord :
                        fromByteArrayBigEndian (out.extract 0 32) < EVM.twoPow 64
                    · have hdecBase := cometRewardsBaseAccrualScale_decode_ok
                        (out := out) hout32 houtSign hbaseWord
                      have hbase64 :
                          (setRewardConfigBaseReturnWord out).toNat < EVM.twoPow 64 := by
                        have hto :
                            (setRewardConfigBaseReturnWord out).toNat =
                              fromByteArrayBigEndian (out.extract 0 32) := by
                          simpa [setRewardConfigBaseReturnWord] using
                            UInt256.toNat_ofNat_of_lt
                              (fromByteArrayBigEndian_extract0_32_lt hout32)
                        rw [hto]
                        exact hbaseWord
                      obtain ⟨kBase, CBase, rdBaseDecoded⟩ :=
                        cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_decode_ok
                          rdPost hout32 houtSize hbase64
                      obtain ⟨cA'', σ''_evm, σ''_solm, A''_solm, zDec, outDec,
                          kDec, CDec, hcallDec, hPostAccountsDec, rdDecPost,
                          houtDecSign⟩ :=
                        cometRewardsSetRewardConfigWithMultiplierX_call_decimals_made
                          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                          (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                          (g := Sat256.ofUInt256 g) (baseOut := out)
                          (baseWord := setRewardConfigBaseReturnWord out)
                          (cA' := cA') (σ'_evm := σ'_evm) (σ'_solm := σ'_solm)
                          (A'_solm := A'_solm)
                          hcanon1 hdepth hPostAccounts rdBaseDecoded hout32 houtSize
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
                              (setRewardConfigWithMultiplierStore I)
                              setRewardConfigWithMultiplierTransition.body .reverted := by
                          exact
                            cometRewardsSetRewardConfigWithMultiplierBodyReverts_decimalsCallFailure
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
                          (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_failure
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
                                (setRewardConfigWithMultiplierStore I)
                                setRewardConfigWithMultiplierTransition.body .reverted := by
                            exact
                              cometRewardsSetRewardConfigWithMultiplierBodyReverts_decimalsDecodeFailure
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
                            (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_short_revert
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
                                      (lt_of_lt_of_le hbase64 (by norm_num [EVM.twoPow, UInt256.size]))
                                  have hrescale :
                                      rescale.toNat =
                                        (setRewardConfigBaseReturnWord out).toNat /
                                          (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat := by
                                    simpa [rescale] using UInt256.toNat_ofNat_of_lt hquotLt
                                  have hbody :
                                      ExecTransitionBody config contract
                                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                        (setRewardConfigWithMultiplierStore I)
                                        setRewardConfigWithMultiplierTransition.body
                                        (.returned
                                          (resumeAfterInternalCall
                                            (setRewardConfigWithMultiplierFrame
                                              (initState cA gh bl σ_solm σ₀
                                                (Sat256.ofUInt256 g) A I) I) "_set" none)
                                          (setRewardConfigSourceFinal evmDecPost I rescale false)
                                          none) := by
                                    exact
                                      cometRewardsSetRewardConfigWithMultiplierBodyReturns_downscale
                                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                        evmPost evmDecPost I
                                        hcanon1
                                        (by simp only [initState]; exact hwv)
                                        (by simp only [initState]; exact hhi)
                                        hgovSolm htokenZeroSolm
                                        (by simpa [evmPost] using hcallS)
                                        hdecBaseReturn
                                        (by simpa [evmPost, evmDecPost] using hcallDec)
                                        hdecDecimalsReturn hle77Return hsafe64Return
                                        hrescale hdown
                                  have hslotPost :
                                      solcSlotWord σ''_evm I
                                          (setRewardConfigWithMultiplierSlotOf I) =
                                        solcSlotWord σ''_solm I
                                          (setRewardConfigWithMultiplierSlotOf I) :=
                                    accountMapEquiv_storage_findD hPostAccountsDec I.codeOwner
                                      (setRewardConfigWithMultiplierSlotOf I) ⟨0⟩
                                  have hIdeal :=
                                    accountMapEquiv_sstoreAccountMap I.codeOwner
                                      (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
                                      (setRewardConfigWithMultiplierMultiplierWord I)
                                      (accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (setRewardConfigWithMultiplierSlotOf I)
                                        (setRewardConfigSlot0Down
                                          (solcSlotWord σ''_solm I
                                            (setRewardConfigWithMultiplierSlotOf I))
                                          (setRewardConfigWithMultiplierTokenWord I) rescale)
                                        hPostAccountsDec)
                                  have hsourceAccounts :=
                                    setRewardConfigSourceFinal_accountMap_equiv evmDecPost I
                                      rescale false
                                  have hAccountsPost := accountMapEquiv.trans
                                    (by simpa [hslotPost] using hIdeal)
                                    (by
                                      simpa [evmDecPost, evmPost, initState, solcSlotWord,
                                        Solm.EVM.storageLoad, State.lookupAccount,
                                        setRewardConfigSlot0Down] using hsourceAccounts)
                                  have hcreated :
                                      cA'' =
                                        (setRewardConfigSourceFinal evmDecPost I rescale false).createdAccounts := by
                                    simp [setRewardConfigSourceFinal,
                                      setRewardConfigSourceAfterShouldUpscale,
                                      setRewardConfigSourceAfterRescale,
                                      setRewardConfigSourceAfterToken, evmDecPost,
                                      storageStore_createdAccounts]
                                  exact
                                    (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_downscale_success
                                        rdDecPost hperm hcanon0 hcanon1 houtDec32 houtDecSize
                                        hdec8Return hle77Return hsafe64Return hbase64 hdown
                                        hrescale)
                                      |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                                        hcreated (by simpa [evmDecPost, hslotPost.symm] using hAccountsPost)
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
                                        (setRewardConfigWithMultiplierStore I)
                                        setRewardConfigWithMultiplierTransition.body .reverted := by
                                      exact
                                        cometRewardsSetRewardConfigWithMultiplierBodyReverts_upscaleZero
                                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                          evmPost evmDecPost I hcanon1
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
                                      (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_upscale_zero_revert
                                          rdDecPost houtDec32 houtDecSize hdec8Return
                                          hle77Return hsafe64Return hbase64 hupLe hbaseWordZero)
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
                                      have hpowLt : (10 : ℕ) ^
                                            (setRewardConfigDecimalsReturnWord outDec).toNat <
                                          2 ^ 64 := by omega
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
                                          (setRewardConfigWithMultiplierStore I)
                                          setRewardConfigWithMultiplierTransition.body
                                          (.returned
                                            (resumeAfterInternalCall
                                              (setRewardConfigWithMultiplierFrame
                                                (initState cA gh bl σ_solm σ₀
                                                  (Sat256.ofUInt256 g) A I) I) "_set" none)
                                            (setRewardConfigSourceFinal evmDecPost I rescale true)
                                            none) := by
                                      exact
                                        cometRewardsSetRewardConfigWithMultiplierBodyReturns_upscale
                                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                          evmPost evmDecPost I hcanon1
                                          (by simp only [initState]; exact hwv)
                                          (by simp only [initState]; exact hhi)
                                          hgovSolm htokenZeroSolm
                                          (by simpa [evmPost] using hcallS)
                                          hdecBaseReturn
                                          (by simpa [evmPost, evmDecPost] using hcallDec)
                                          hdecDecimalsReturn hle77Return hsafe64Return
                                          hrescale hupLe hbaseZero
                                    have hslotPost :
                                        solcSlotWord σ''_evm I
                                            (setRewardConfigWithMultiplierSlotOf I) =
                                          solcSlotWord σ''_solm I
                                            (setRewardConfigWithMultiplierSlotOf I) :=
                                      accountMapEquiv_storage_findD hPostAccountsDec I.codeOwner
                                        (setRewardConfigWithMultiplierSlotOf I) ⟨0⟩
                                    have hIdeal :=
                                      accountMapEquiv_sstoreAccountMap I.codeOwner
                                        (setRewardConfigWithMultiplierSlotOf I + ⟨1⟩)
                                        (setRewardConfigWithMultiplierMultiplierWord I)
                                        (accountMapEquiv_sstoreAccountMap I.codeOwner
                                          (setRewardConfigWithMultiplierSlotOf I)
                                          (setRewardConfigSlot0Up
                                            (solcSlotWord σ''_solm I
                                              (setRewardConfigWithMultiplierSlotOf I))
                                            (setRewardConfigWithMultiplierTokenWord I) rescale)
                                          hPostAccountsDec)
                                    have hsourceAccounts :=
                                      setRewardConfigSourceFinal_accountMap_equiv evmDecPost I
                                        rescale true
                                    have hAccountsPost := accountMapEquiv.trans
                                      (by simpa [hslotPost] using hIdeal)
                                      (by
                                        simpa [evmDecPost, evmPost, initState, solcSlotWord,
                                          Solm.EVM.storageLoad, State.lookupAccount,
                                          setRewardConfigSlot0Up] using hsourceAccounts)
                                    have hcreated :
                                        cA'' =
                                          (setRewardConfigSourceFinal evmDecPost I rescale true).createdAccounts := by
                                      simp [setRewardConfigSourceFinal,
                                        setRewardConfigSourceAfterShouldUpscale,
                                        setRewardConfigSourceAfterRescale,
                                        setRewardConfigSourceAfterToken, evmDecPost,
                                        storageStore_createdAccounts]
                                    exact
                                      (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_upscale_success
                                          rdDecPost houtDec32 houtDecSize hdec8Return
                                          hle77Return hsafe64Return hbase64 hperm hcanon0
                                          hcanon1 hupLe hbaseZero hrescale)
                                        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                                          hcreated (by simpa [evmDecPost, hslotPost.symm] using hAccountsPost)
                                          (returnEquiv.fallthrough rfl (by rfl) (by native_decide))
                              · have hgt64 :
                                    2 ^ 64 - 1 <
                                      (10 : ℕ) ^
                                        fromByteArrayBigEndian (outDec.extract 0 32) :=
                                  Nat.lt_of_not_ge hsafe64
                                have hbody :
                                    ExecTransitionBody config contract
                                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                                      (setRewardConfigWithMultiplierStore I)
                                      setRewardConfigWithMultiplierTransition.body .reverted := by
                                  exact
                                    cometRewardsSetRewardConfigWithMultiplierBodyReverts_safe64Failure
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
                                  (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_safe64_revert
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
                                    (setRewardConfigWithMultiplierStore I)
                                    setRewardConfigWithMultiplierTransition.body .reverted := by
                                exact
                                  cometRewardsSetRewardConfigWithMultiplierBodyReverts_pow10Failure
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
                                (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_pow10_revert
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
                                  (setRewardConfigWithMultiplierStore I)
                                  setRewardConfigWithMultiplierTransition.body .reverted := by
                              exact
                                cometRewardsSetRewardConfigWithMultiplierBodyReverts_decimalsDecodeFailure
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
                              (cometRewardsSetRewardConfigWithMultiplierX_after_decimals_noncanon_revert
                                  rdDecPost houtDec32 houtDecSize hdecNo)
                                |>.reEquivExecutionRevert hcode hd hdec hbody
                    · have hdecBase := cometRewardsBaseAccrualScale_decode_none_noncanon
                        (out := out) hout32 houtSign hbaseWord
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (setRewardConfigWithMultiplierStore I)
                            setRewardConfigWithMultiplierTransition.body .reverted := by
                        exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseDecodeFailure
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
                        (cometRewardsSetRewardConfigWithMultiplierX_after_baseAccrualScale_noncanon_revert
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
                            (setRewardConfigWithMultiplierCometWord I).toNat))).substate }
                have hcallS :
                    typedCallViaEVM config evmInit
                      (EVM.address (AccountAddress.ofNat
                        (setRewardConfigWithMultiplierCometWord I).toNat))
                      "baseAccrualScale" 0 []
                      (false, evmFail, ByteArray.empty) false := by
                  exact callNotMade_depthLimit
                    (cfg := config) (evm := evmInit)
                    (tgt := EVM.address (AccountAddress.ofNat
                      (setRewardConfigWithMultiplierCometWord I).toNat))
                    (name := "baseAccrualScale") (args := [])
                    (calldata := (setRewardConfigBaseAccrualScaleCalldataMem I)
                      |>.readWithPadding 128 4)
                    (callPerm := false)
                    (setRewardConfigBaseAccrualScaleCalldataMem_encode I)
                    (by simpa [evmInit, initState] using hdepth1024)
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (setRewardConfigWithMultiplierStore I)
                      setRewardConfigWithMultiplierTransition.body .reverted := by
                  exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_baseCallFailure
                    evmInit evmFail I
                    (by simp only [evmInit, initState]; exact hwv)
                    (by simp only [evmInit, initState]; exact hhi)
                    (by simpa [evmInit] using hgovSolm)
                    (by simpa [evmInit] using htokenZeroSolm)
                    hcallS
                exact (cometRewardsSetRewardConfigWithMultiplierX_baseAccrualScale_callDepthLimit
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    hwv hsz100 hsize hhi hcanon0 hcanon1 hauth htokenZero hreach
                    hdepth1024)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hauthSolm :
                governorReturnWord σ_solm I ≠ solcSourceWord I := by
              intro hbad
              exact hauth (by
                rw [hgovRet]
                exact hbad)
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (setRewardConfigWithMultiplierStore I)
                  setRewardConfigWithMultiplierTransition.body .reverted := by
              exact cometRewardsSetRewardConfigWithMultiplierBodyReverts_auth
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
                (by simp only [initState]; exact hhi)
                (by
                  simpa [governorReturnWord, governorWord, initState, Solm.EVM.storageLoad,
                    State.lookupAccount] using hauthSolm)
            exact (cometRewardsSetRewardConfigWithMultiplierX_revert_auth
                (g := Sat256.ofUInt256 g)
                hwv hsz100 hsize hhi hcanon0 hcanon1 hauth hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec :=
            cometRewardsDecode_setRewardConfigWithMultiplier_none_noncanon_token
              (I := I) hsz100 hhi hcanon0 hcanon1
          have hnc : UInt256.eq (setRewardConfigWithMultiplierTokenWord I)
              (UInt256.land (setRewardConfigWithMultiplierTokenWord I) solcAddrMask) =
                ⟨0⟩ :=
            uInt256_eq_zero_of_ne
              (fun he => hcanon1 (solcAddrCanonical_of_clean he))
          exact (cometRewardsSetRewardConfigWithMultiplierX_noncanon_token
              (g := Sat256.ofUInt256 g)
              hwv hsz100 hsize hhi hcanon0 hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec :=
          cometRewardsDecode_setRewardConfigWithMultiplier_none_noncanon_comet
            (I := I) hsz100 hhi hcanon0
        have hnc : UInt256.eq (setRewardConfigWithMultiplierCometWord I)
            (UInt256.land (setRewardConfigWithMultiplierCometWord I) solcAddrMask) =
              ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanon0 (solcAddrCanonical_of_clean he))
        exact (cometRewardsSetRewardConfigWithMultiplierX_noncanon_comet
            (g := Sat256.ofUInt256 g)
            hwv hsz100 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_setRewardConfigWithMultiplier_none_huge (I := I) hbig
      exact (cometRewardsSetRewardConfigWithMultiplierX_hugearg
          (g := Sat256.ofUInt256 g) hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec :=
      cometRewardsDecode_setRewardConfigWithMultiplier_none_short (I := I) hsz4 hshort
    exact (cometRewardsSetRewardConfigWithMultiplierX_shortarg
        (g := Sat256.ofUInt256 g) hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
