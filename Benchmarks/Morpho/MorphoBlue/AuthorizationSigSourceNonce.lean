import Benchmarks.Morpho.MorphoBlue.AuthorizationSigSourceDecode
import Benchmarks.Morpho.MorphoBlue.StateBlock
import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def AuthorizationWords.fieldValue (a : AuthorizationWords) (i : Fin 5) : Value :=
  match i.val with
  | 0 => .address (AccountAddress.ofNat a.authorizer.toNat)
  | 1 => .address (AccountAddress.ofNat a.authorized.toNat)
  | 2 => .bool (decide (a.enabled ≠ ⟨0⟩))
  | 3 => .int (Int.ofNat a.nonce.toNat)
  | _ => .int (Int.ofNat a.deadline.toNat)

structure AuthorizationLocals (a : AuthorizationWords) (cd : ByteArray) (locals : Store) : Prop where
  auth : locals.get? "authorization" = some a.value
  calldata : locals.get? "__calldata" = some (.bytes cd)
  nonce : locals.get? "nonce" = none
  authorized : locals.get? "isAuthorized" = none

theorem AuthorizationLocals.insert {a cd locals} (hl : AuthorizationLocals a cd locals)
    (name : Ident) (value : Value)
    (hn : name ≠ "authorization" ∧ name ≠ "__calldata" ∧ name ≠ "nonce" ∧ name ≠ "isAuthorized") :
    AuthorizationLocals a cd (locals.insert name value) := by
  constructor
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using hn.1)]; exact hl.auth
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using hn.2.1)]; exact hl.calldata
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using hn.2.2.1)]; exact hl.nonce
  · rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using hn.2.2.2)]; exact hl.authorized

theorem authorizationDecodedFrame_locals (cd : ByteArray) (v : MorphoImmutables) :
    AuthorizationLocals (authorizationFromCalldata cd) cd (authorizationDecodedFrame cd v).locals := by
  constructor
  · exact store_get_self _ _ _
  · exact authorizationDecodedFrame_calldata cd v
  · simp [authorizationDecodedFrame, fallbackLocals]
  · simp [authorizationDecodedFrame, fallbackLocals]

theorem AuthorizationLocals.evalField {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (i : Fin 5) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "authorization") i.val) = .ok (a.fieldValue i) := by
  fin_cases i <;> simp only [evalExpr?, hl.auth, AuthorizationWords.value,
    AuthorizationWords.fieldValue, tupleGetValue?, EvalResult.bind, EvalResult.ofOption, bind] <;> rfl

theorem AuthorizationLocals.evalTimestamp {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .le (.env .timestamp) (.tupleGet (.var "authorization") 4)) =
      .ok (.bool (decide ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤ a.deadline.toNat))) := by
  have ht := hl.evalField imms evm ⟨4, by decide⟩
  rw [evalExpr_binary_nonshort (by decide) (by decide), ht]
  simp only [evalExpr?, envValue, AuthorizationWords.fieldValue, pure, bind, EvalResult.bind,
    evalBinaryOp?]
  simp

def authorizationNonceSlot (a : AuthorizationWords) : UInt256 := solcMappingSlot ⟨7⟩ a.authorizer

def authorizationUsedNonce (a : AuthorizationWords) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (authorizationNonceSlot a) σ I

theorem AuthorizationLocals.evalNonce {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (hc : a.Canonical) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.storage ⟨"nonce", [.mindex (.tupleGet (.var "authorization") 0)]⟩) =
      .ok (.int (Int.ofNat (authorizationUsedNonce a evm.accountMap evm.executionEnv).toNat)) :=
  evalMorphoNonce evm locals imms _ a.authorizer hl.nonce
    (by simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨0, by decide⟩) hc.1

def authorizationUsedFrame (frame : Frame) (n : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "usedNonce" (.int (Int.ofNat n.toNat)) }

theorem morphoAuthorizationNonceSourceStart (evm : EVM.State) (v : MorphoImmutables)
    (hb : AuthorizationSigBounds evm.executionEnv.calldata)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsel : selIs evm.executionEnv (morphoSelBytes 27))
    (ht : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≤
      (authorizationFromCalldata evm.executionEnv.calldata).deadline.toNat) :
    ABlock config evm (authorizationSigFrame evm.executionEnv.calldata v)
      setAuthorizationWithSigTransition.body
      (authorizationUsedFrame (authorizationDecodedFrame evm.executionEnv.calldata v)
        (authorizationUsedNonce (authorizationFromCalldata evm.executionEnv.calldata)
          evm.accountMap evm.executionEnv))
      (setAuthorizationWithSigTransition.body.drop 12) := by
  have hl := authorizationDecodedFrame_locals evm.executionEnv.calldata v
  have p0 := (morphoAuthorizationSigSourceDecode evm v hcv hsel hb).requireStep
    (by simpa only [ht, decide_true] using hl.evalTimestamp (immStore v) evm)
  exact p0.letStep (hl.evalNonce (immStore v) evm hb.2.2)

def storeAuthorizationNonce (evm : EVM.State) (a : AuthorizationWords) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (authorizationNonceSlot a) value

theorem AuthorizationLocals.assignNonce {a cd locals} (hl : AuthorizationLocals a cd locals)
    (imms : Store) (evm : EVM.State) (hc : a.Canonical) (value : UInt256) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"nonce", [.mindex (.tupleGet (.var "authorization") 0)]⟩
      (.int (Int.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        storeAuthorizationNonce evm a value) := by
  apply assignStorageRef_storage_scalar_value hl.nonce
    (er := ⟨"nonce", [.mindex (.address (AccountAddress.ofNat a.authorizer.toNat))]⟩)
  · have he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.tupleGet (.var "authorization") 0) =
        .ok (.address (AccountAddress.ofNat a.authorizer.toNat)) := by
      simpa only [AuthorizationWords.fieldValue] using hl.evalField imms evm ⟨0, by decide⟩
    exact evalStorageRef_mindex he rfl
  · rfl
  · rfl
  · exact morphoLayout_nonce a.authorizer hc.1
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint256 evm _ value

theorem authorizationUsedFrame_eval (frame : Frame) (evm : EVM.State) (n : UInt256) :
    evalExpr? config (authorizationUsedFrame frame n) evm (.var "usedNonce") =
      .ok (.int (Int.ofNat n.toNat)) := by
  simp only [evalExpr?, authorizationUsedFrame, store_get_self, EvalResult.ofOption]

theorem morphoAuthorizationNonceSourceExpr (frame : Frame) (evm : EVM.State) (n : UInt256)
    (hn : n.toNat + 1 < UInt256.size) :
    evalExpr? config (authorizationUsedFrame frame n) evm
      (.inRange (.uint ⟨256, by decide⟩) (.binary .add (.var "usedNonce") (.intLit 1))) =
      .ok (.int (Int.ofNat (n + UInt256.ofNat 1).toNat)) :=
  checkedAddSourceOk (authorizationUsedFrame_eval frame evm n) (by simp only [evalExpr?, pure]; rfl) hn

theorem morphoAuthorizationNonceSourceOverflow (frame : Frame) (evm : EVM.State) (n : UInt256)
    (hn : UInt256.size ≤ n.toNat + 1) :
    ExecBlock config (authorizationUsedFrame frame n) evm
      (setAuthorizationWithSigTransition.body.drop 12) .reverted :=
  ExecBlock.consRevert (ExecStmt.assignExprRevert
    (checkedAddSourceOverflow (authorizationUsedFrame_eval frame evm n)
      (b := UInt256.ofNat 1) (by simp only [evalExpr?, pure]; rfl) hn))

end Benchmarks.Morpho.MorphoBlue
