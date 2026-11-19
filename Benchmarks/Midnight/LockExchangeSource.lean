import Benchmarks.Midnight.LockSource
import Reasoning.ExternalCall

/-! Source evaluation of the transient lock exchange used around trade callbacks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

abbrev tExchangeFunction : FunctionDecl := contract.functions[12]!

def lockStorageRef : StorageRef :=
  { base := "locks", steps := [.mindex (.var "baseSlot"), .mindex (.var "key1"),
      .mindex (.var "key2")] }

def lockEvalRef (base id user : UInt256) : EvaledStorageRef :=
  { base := "locks", steps := [.mindex (.int base.toNat),
      .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .mindex (.address (AccountAddress.ofNat user.toNat))] }

theorem evalLockStorageRef {frame : Frame} {evm : State} {base id user : UInt256}
    (hb : frame.locals.get? "baseSlot" = some (.int base.toNat))
    (hi : frame.locals.get? "key1" = some (wordBytes32Value id))
    (hu : frame.locals.get? "key2" = some (.address (AccountAddress.ofNat user.toNat))) :
    evalTransientStorageRef config frame evm lockStorageRef = .ok (lockEvalRef base id user) := by
  have hlen : (EVM.Word.toBytesBE id).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size id
  simp only [lockStorageRef, lockEvalRef, evalTransientStorageRef,
    evalTransientStorageRefSteps, evalTransientStorageRefStep, evalExpr?, hb, hi, hu,
    EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind, hlen,
    show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]

theorem lockEvalRef_layout {base id user : UInt256} (hc : user.toNat < EVM.addressModulus) :
    Model.lockLayout (lockEvalRef base id user) = some (.leaf (uint256Loc (lockSlot base id user)))
    := by
  simp only [lockEvalRef, Model.lockLayout, bne_self_eq_false, Bool.false_eq_true, if_false,
    word_toBytesBE_toByteArray_eq_toByteArray]
  have hu : EVM.word (AccountAddress.ofNat user.toNat).toNat = user := by
    change UInt256.ofNat (user.toNat % EVM.addressModulus) = user
    rw [Nat.mod_eq_of_lt hc]
    exact u256_ofNat_toNat user
  have hb : EVM.wordOfInt (base.toNat : Int) = base := wordOfInt_ofNat_toNat base
  rw [hu, hb]
  rfl

theorem evalLockNonzero {frame : Frame} {evm : State} {base id user : UInt256}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hb : frame.locals.get? "baseSlot" = some (.int base.toNat))
    (hi : frame.locals.get? "key1" = some (wordBytes32Value id))
    (hu : frame.locals.get? "key2" = some (.address (AccountAddress.ofNat user.toNat))) :
    evalExpr? config frame evm (.binary .ne (.transient lockStorageRef) (.intLit 0)) =
      .ok (lockValue evm base id user) := by
  have hread := evalExpr_transient_scalar_value (evalLockStorageRef hb hi hu)
    (t := .int (.uint ⟨256, by decide⟩)) (by rw [hc]; rfl) rfl (lockEvalRef_layout hcanon)
    (transientLocLoad_uint256 evm (lockSlot base id user))
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

theorem assignLockWord {frame : Frame} {evm : State} {base id user : UInt256} (value : UInt256)
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hb : frame.locals.get? "baseSlot" = some (.int base.toNat))
    (hi : frame.locals.get? "key1" = some (wordBytes32Value id))
    (hu : frame.locals.get? "key2" = some (.address (AccountAddress.ofNat user.toNat))) :
    assignStorageRef? config frame evm .transient lockStorageRef (.int value.toNat) =
      .ok (frame, Stele.EVM.transientStore evm evm.executionEnv.codeOwner
        (lockSlot base id user) value) :=
  assignStorageRef_transient_scalar_value (evalLockStorageRef hb hi hu)
    (by rw [hc]; rfl) rfl (lockEvalRef_layout hcanon) (Or.inl ⟨_, rfl⟩)
    (transientLocStore_uint256 evm _ value)

def lockExchangeState (evm : State) (base id user : UInt256) (value : Bool) : State :=
  Stele.EVM.transientStore evm evm.executionEnv.codeOwner (lockSlot base id user)
    (if value then ⟨1⟩ else ⟨0⟩)

def lockExchangeFrame (frame : Frame) (evm : State) (base id user : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "previous" (lockValue evm base id user) }

theorem lockExchangeBody {frame : Frame} {evm : State} {base id user : UInt256} {value : Bool}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (hb : frame.locals.get? "baseSlot" = some (.int base.toNat))
    (hi : frame.locals.get? "key1" = some (wordBytes32Value id))
    (hu : frame.locals.get? "key2" = some (.address (AccountAddress.ofNat user.toNat)))
    (hv : frame.locals.get? "value" = some (.bool value)) (hp : evm.executionEnv.perm = true) :
    ExecFuncBody config frame evm tExchangeFunction.body
      (.returned (lockExchangeFrame frame evm base id user)
        (lockExchangeState evm base id user value) (some [lockValue evm base id user])) := by
  have hb' : (lockExchangeFrame frame evm base id user).locals.get? "baseSlot" =
      some (.int base.toNat) := (store_get_ne _ _ (by decide)).trans hb
  have hi' : (lockExchangeFrame frame evm base id user).locals.get? "key1" =
      some (wordBytes32Value id) := (store_get_ne _ _ (by decide)).trans hi
  have hu' : (lockExchangeFrame frame evm base id user).locals.get? "key2" =
      some (.address (AccountAddress.ofNat user.toNat)) := (store_get_ne _ _ (by decide)).trans hu
  have hv' : (lockExchangeFrame frame evm base id user).locals.get? "value" =
      some (.bool value) := (store_get_ne _ _ (by decide)).trans hv
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalLockNonzero hc hcanon hb hi hu))
  apply ExecBlock.consNormal (stele' := lockExchangeFrame frame evm base id user)
    (evm' := lockExchangeState evm base id user value)
  · apply ExecStmt.assign (Or.inr hp)
      (value := .int (if value then (⟨1⟩ : UInt256) else ⟨0⟩).toNat)
    · change evalExpr? config (lockExchangeFrame frame evm base id user) evm
        (.ite (.var "value") (.intLit 1) (.intLit 0)) = _
      cases value <;> simp only [evalExpr?, hv', EvalResult.ofOption, EvalResult.bind, bind, pure]
      all_goals rfl
    · exact assignLockWord (frame := lockExchangeFrame frame evm base id user)
        _ hc hcanon hb' hi' hu'
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    simp only [evalExprs?, evalExpr?, lockExchangeFrame, store_get_self,
      EvalResult.ofOption, EvalResult.bind, bind, pure]

def tExchangeArguments (base id user : UInt256) (value : Bool) : Store :=
  ((((∅ : Store).insert "value" (.bool value)).insert "key2"
    (.address (AccountAddress.ofNat user.toNat))).insert "key1"
    (wordBytes32Value id)).insert "baseSlot" (.int base.toNat)

theorem callLockExchange {frame : Frame} {evm : State} {base id user : UInt256}
    {value : Bool} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract) (hcanon : user.toNat < EVM.addressModulus)
    (he : evalExprs? config frame evm args = .ok
      [.int base.toNat, wordBytes32Value id, .address (AccountAddress.ofNat user.toNat), .bool value])
    (hp : evm.executionEnv.perm = true) :
    ExecStmt config frame evm (.internalCall "UtilsLib_tExchange" args name)
      (.ok (resumeAfterInternalCall frame name (some [lockValue evm base id user]))
        (lockExchangeState evm base id user value)) := by
  apply internalCallFunctionReturn (callee := tExchangeFunction)
    (locals := tExchangeArguments base id user value) he
  · rw [hc]; rfl
  · rfl
  · apply lockExchangeBody (frame :=
      { frame with locals := tExchangeArguments base id user value }) hc hcanon
    · exact store_get_self _ _ _
    · unfold tExchangeArguments
      rw [store_get_ne _ _ (by decide), store_get_self]
    · unfold tExchangeArguments
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
    · unfold tExchangeArguments
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide), store_get_self]
    · exact hp

-- LIBRARY CANDIDATE: transient reads depend only on the shared account map and environment.
theorem sourceState_transientRead {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot : UInt256) :
    Stele.EVM.transientLoad evm evm.executionEnv.codeOwner slot =
      codeOwnerTransientWord I σ slot := by
  simp [codeOwnerTransientWord, Stele.EVM.transientLoad, State.lookupAccount,
    Account.lookupTransientStorage, ← hs.accounts, hs.env]

-- LIBRARY CANDIDATE: paired transient writes preserve source/runtime state agreement.
theorem sourceState_transientWrite {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot word : UInt256) :
    SourceState s0 I (tstoreAccountMap I.codeOwner σ slot word)
      (Stele.EVM.transientStore evm evm.executionEnv.codeOwner slot word) := by
  refine ⟨(transientStore_σ₀ ..).trans hs.world,
    (transientStore_executionEnv ..).trans hs.env, ?_⟩
  rw [transientStore_accountMap, hs.env, ← hs.accounts]

end Benchmarks.Midnight
