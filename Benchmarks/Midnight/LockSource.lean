import Benchmarks.Midnight.InternalCall
import Benchmarks.Midnight.PositionStorage
import Reasoning.TransientStorage

variable {fork : Ethereum.Fork}

/-! Internal source helpers for Midnight's transient liquidation lock. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

abbrev tGetFunction : FunctionDecl := contract.functions[26]!
abbrev liquidationLockedFunction : FunctionDecl := contract.functions[14]!

def liquidationLockBase : UInt256 :=
  UInt256.ofNat 65530685186148139943160654700974242543032290443373287283358098694458470976932

def lockSlot (base id user : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (id.toByteArray ++ user.toByteArray ++ base.toByteArray))

def tGetArguments (base id user : UInt256) : Store :=
  (((∅ : Store).insert "key2" (.address (AccountAddress.ofNat user.toNat))).insert "key1"
    (wordBytes32Value id)).insert "baseSlot" (.int (Int.ofNat base.toNat))

def lockValue (evm : EVM.State) (base id user : UInt256) : Value :=
  wordToElem .bool (Stele.EVM.transientLoad evm evm.executionEnv.codeOwner (lockSlot base id user))

theorem tGetBodyReturns (evm : EVM.State) (imms : Store) (base id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) :
    ExecFuncBody fork config { contract := contract, locals := tGetArguments base id user, immutables := imms }
      evm tGetFunction.body
      (.returned { contract := contract, locals := tGetArguments base id user, immutables := imms }
        evm (some [lockValue evm base id user])) := by
  have hbase : (tGetArguments base id user).get? "baseSlot" =
      some (.int (Int.ofNat base.toNat)) := by
    exact store_get_self _ _ _
  have hid : (tGetArguments base id user).get? "key1" = some (wordBytes32Value id) := by
    unfold tGetArguments
    rw [store_get_ne _ _ (by decide), store_get_self]
  have huser : (tGetArguments base id user).get? "key2" =
      some (.address (AccountAddress.ofNat user.toNat)) := by
    unfold tGetArguments
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  have hread : evalExpr? config
      { contract := contract, locals := tGetArguments base id user, immutables := imms } evm
      (.transient { base := "locks", steps := [.mindex (.var "baseSlot"), .mindex (.var "key1"),
        .mindex (.var "key2")] }) =
      .ok (.int (Int.ofNat (Stele.EVM.transientLoad evm evm.executionEnv.codeOwner
        (lockSlot base id user)).toNat)) := by
    apply evalExpr_transient_scalar_value (loc := uint256Loc (lockSlot base id user))
      (er := { base := "locks", steps := [.mindex (.int (Int.ofNat base.toNat)),
        .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
        .mindex (.address (AccountAddress.ofNat user.toNat))] }) (t := .int (.uint ⟨256, by decide⟩))
    · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
        simpa using word_toBytesBE_toByteArray_size id
      simp only [evalTransientStorageRef, evalTransientStorageRefSteps, evalTransientStorageRefStep,
        evalExpr?, hbase, hid, huser, EvalResult.bind, EvalResult.ofOption, valueToKey?,
        wordBytes32Value, pure, bind, hlen, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
    · rfl
    · rfl
    · simp only [Model.lockLayout, bne_self_eq_false, Bool.false_eq_true, if_false,
        word_toBytesBE_toByteArray_eq_toByteArray]
      have hu : EVM.word (AccountAddress.ofNat user.toNat).toNat = user := by
        change UInt256.ofNat (user.toNat % EVM.addressModulus) = user
        rw [Nat.mod_eq_of_lt hcanon]
        exact u256_ofNat_toNat user
      rw [hu, wordOfInt_ofNat_toNat]
      rfl
    · exact transientLocLoad_uint256 evm _
  apply ExecFuncBody.execBlockRet
  apply ABlock.returns ABlock.start
  change evalExpr? config
    { contract := contract, locals := tGetArguments base id user, immutables := imms } evm
    (.binary .ne (.transient _) (.intLit 0)) = .ok _
  rw [evalExpr_binary_nonshort (by decide) (by decide), hread]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp_ne_int_ok]
  let w := Stele.EVM.transientLoad evm evm.executionEnv.codeOwner (lockSlot base id user)
  change EvalResult.ok (.bool (!(Value.int (Int.ofNat w.toNat) == Value.int 0))) =
    .ok (wordToElem .bool w)
  by_cases hw : w = ⟨0⟩
  · rw [hw]; rfl
  · have hn : Int.ofNat w.toNat ≠ 0 := by
      intro he
      apply hw
      apply u256_inj
      simpa using congrArg Int.toNat he
    rw [valueInt_beq_false_of_ne hn, wordToElemBool, decide_eq_false hw]

theorem liquidationLockBase_cast :
    castValue? (.fixedBytes ⟨31, by decide⟩
      (KEC "morpho.midnight.liquidationLocked".toByteArray).toList)
      (.elem (.int (.uint ⟨256, by decide⟩))) =
      some (.int (Int.ofNat liquidationLockBase.toNat)) := by native_decide

theorem evalLiquidationLockBase (cfg : Config) (frame : Frame) (evm : EVM.State) :
    evalExpr? cfg frame evm (.cast
      (.keccak256 (.bytesLit "morpho.midnight.liquidationLocked".toByteArray))
      (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat liquidationLockBase.toNat)) := by
  simp only [evalExpr?, bind, pure, EvalResult.bind, liquidationLockBase_cast, EvalResult.ofOption]

theorem positionArguments_id (id user : UInt256) :
    (positionArguments id user).get? "id" = some (wordBytes32Value id) := by
  unfold positionArguments
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem positionArguments_user (id user : UInt256) :
    (positionArguments id user).get? "user" =
      some (.address (AccountAddress.ofNat user.toNat)) := store_get_self _ _ _

def lockBodyArguments (id user : UInt256) : Store :=
  ((∅ : Store).insert "user" (.address (AccountAddress.ofNat user.toNat))).insert "id"
    (wordBytes32Value id)

theorem lockBodyArguments_id (id user : UInt256) :
    (lockBodyArguments id user).get? "id" = some (wordBytes32Value id) := store_get_self _ _ _

theorem lockBodyArguments_user (id user : UInt256) :
    (lockBodyArguments id user).get? "user" =
      some (.address (AccountAddress.ofNat user.toNat)) := by
  unfold lockBodyArguments
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem liquidationLockedInternalReturns (evm : EVM.State) (imms : Store) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) :
    ExecFuncBody fork config { contract := contract, locals := lockBodyArguments id user, immutables := imms }
      evm liquidationLockedFunction.body
      (.returned (resumeAfterInternalCall
        { contract := contract, locals := lockBodyArguments id user, immutables := imms }
        "__c0" (some [lockValue evm liquidationLockBase id user]))
        evm (some [lockValue evm liquidationLockBase id user])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (stele' := resumeAfterInternalCall _ "__c0"
    (some [lockValue evm liquidationLockBase id user]))
  · apply internalCallFunctionReturn (callee := tGetFunction)
      (locals := tGetArguments liquidationLockBase id user)
      (argVals := [.int (Int.ofNat liquidationLockBase.toNat), wordBytes32Value id,
        .address (AccountAddress.ofNat user.toNat)])
    · change evalExprs? config
        { contract := contract, locals := lockBodyArguments id user, immutables := imms } evm
        [.cast (.keccak256 (.bytesLit "morpho.midnight.liquidationLocked".toByteArray))
          (.elem (.int (.uint ⟨256, by decide⟩))), .var "id", .var "user"] = .ok _
      rw [evalExprs?, evalLiquidationLockBase]
      simp only [evalExprs?, evalExpr?, lockBodyArguments_id, lockBodyArguments_user,
        EvalResult.ofOption, bind, pure, EvalResult.bind]
    · rfl
    · rfl
    · exact tGetBodyReturns evm imms liquidationLockBase id user hcanon
  · exact returnInternalResult "__c0" _

theorem liquidationLockedBodyReturns (evm : EVM.State) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm (positionArguments id user) liquidationLockedTransition.body
      (.returned (resumeAfterInternalCall (calldataFrame contract (positionArguments id user) ∅ evm)
        "__r" (some [lockValue evm liquidationLockBase id user]))
        evm (some [lockValue evm liquidationLockBase id user])) := by
  apply ExecFuncBody.execBlockRet
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consNormal (stele' := resumeAfterInternalCall _ "__r"
    (some [lockValue evm liquidationLockBase id user]))
  · apply internalCallFunctionReturn (callee := liquidationLockedFunction)
      (locals := lockBodyArguments id user)
      (argVals := [wordBytes32Value id, .address (AccountAddress.ofNat user.toNat)])
    · have hid : (calldataFrame contract (positionArguments id user) ∅ evm).locals.get? "id" =
          some (wordBytes32Value id) := by
        change ((positionArguments id user).insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
          "id" = _
        rw [store_get_ne _ _ (by decide), positionArguments_id]
      have huser : (calldataFrame contract (positionArguments id user) ∅ evm).locals.get? "user" =
          some (.address (AccountAddress.ofNat user.toNat)) := by
        change ((positionArguments id user).insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
          "user" = _
        rw [store_get_ne _ _ (by decide), positionArguments_user]
      simp only [evalExprs?, evalExpr?, hid, huser, EvalResult.ofOption, bind, pure, EvalResult.bind]
    · rfl
    · rfl
    · exact liquidationLockedInternalReturns evm ∅ id user hcanon
  · exact returnInternalResult "__r" _

end Benchmarks.Midnight
