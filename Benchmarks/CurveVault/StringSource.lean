import Benchmarks.CurveVault.StringArithmetic
import Benchmarks.CurveVault.Arithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringName (isName : Bool) : Ident := if isName then "name" else "symbol"
def vaultStringSlot (isName : Bool) : UInt256 := if isName then ⟨6⟩ else ⟨9⟩
def vaultStringBody (isName : Bool) : List Stmt := if isName then nameTransition.body else symbolTransition.body

def vaultStringBytes (evm : State) (slot : UInt256) : ByteArray :=
  let length := (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat
  (vyperReadDataWords evm slot 0 ((length + 31) / 32)).extract 0 length

def vaultStringLocals (length : UInt256) : Store :=
  (∅ : Store).insert "stored_length" (.int (Int.ofNat length.toNat))

abbrev vaultStringWrapExpr : Expr := .binary .and
  (.binary .ge (.var "stored_length") (.binary .sub (.intLit (Int.ofNat (UInt256.size - 1))) (.intLit 62)))
  (.binary .le (.var "stored_length") (.binary .sub (.intLit (Int.ofNat (UInt256.size - 1))) (.intLit 31)))

theorem vaultStringBody_eq (isName : Bool) : vaultStringBody isName =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "stored_length" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.arrayLength .storage {base := vaultStringName isName, steps := []}),
      .ite vaultStringWrapExpr [.return [.bytesLit ByteArray.empty]] [],
      .require (.binary .le (.var "stored_length") (.intLit 64)),
      .return [.storage {base := vaultStringName isName, steps := []}]] := by
  cases isName <;> rfl

theorem vaultStringResolve (evm : State) (locals : Store) (isName : Bool)
    (hbase : locals.get? (vaultStringName isName) = none) :
    resolveStorageRef? config {contract := contract, locals := locals} evm
      {base := vaultStringName isName, steps := []} =
      .ok ({base := vaultStringName isName, steps := []}, StorageType.string) := by
  apply resolveStorageRef?_ok hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
  cases isName <;> rfl

theorem vaultStringLengthEval (evm : State) (locals : Store) (isName : Bool)
    (hbase : locals.get? (vaultStringName isName) = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.arrayLength .storage {base := vaultStringName isName, steps := []}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat)) := by
  rw [evalExpr?]
  simp only [vaultStringResolve evm locals isName hbase, EvalResult.bind, bind]
  cases isName <;> rfl

theorem vaultStringValueEval (evm : State) (locals : Store) (isName : Bool)
    (hbase : locals.get? (vaultStringName isName) = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := vaultStringName isName, steps := []}) =
      .ok (.bytes (vaultStringBytes evm (vaultStringSlot isName))) := by
  rw [evalExpr?]
  simp only [vaultStringResolve evm locals isName hbase, EvalResult.bind, bind]
  change vyperReadRaw? boundedStorage.locate? _ evm
    {base := vaultStringName isName, steps := []} .string = _
  rw [vyperReadRaw?]
  cases isName <;> rfl

theorem vaultStringWrapEval (evm : State) (locals : Store) (length : UInt256)
    (hlen : locals.get? "stored_length" = some (.int (Int.ofNat length.toNat))) :
    evalExpr? config {contract := contract, locals := locals} evm vaultStringWrapExpr =
      .ok (.bool (decide (UInt256.size - 63 ≤ length.toNat) && decide (length.toNat ≤ UInt256.size - 32))) := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hlen
  by_cases hlo : UInt256.size - 63 ≤ length.toNat <;>
    simp [vaultStringWrapExpr, evalExpr?, heval, evalBinaryOp?, EvalResult.bind, pure, bind,
      UInt256.size, Int.ofNat_eq_natCast] at hlo ⊢ <;> simp_all
  simp only [Nat.not_le_of_lt hlo, decide_false, Bool.false_and]

theorem vaultStringSourcePrefix (evm : State) (isName : Bool)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := ∅} evm
      [.require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "stored_length" (some (.elem (.int (.uint ⟨256, by decide⟩))))
          (.arrayLength .storage {base := vaultStringName isName, steps := []})]
      (.ok {contract := contract, locals := vaultStringLocals (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName))} evm) :=
  ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue))
    (ExecBlock.consNormal (ExecStmt.letDecl (vaultStringLengthEval evm ∅ isName (by simp))) ExecBlock.nil)

theorem vaultStringSourceReturns (evm : State) (isName : Bool)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat ≤ 64) :
    ExecTransitionBody fork config contract evm ∅ (vaultStringBody isName)
      (.returned {contract := contract, locals := vaultStringLocals (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName))}
        evm (some [.bytes (vaultStringBytes evm (vaultStringSlot isName))])) := by
  let length := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)
  let locals := (∅ : Store).insert "stored_length" (.int (Int.ofNat length.toNat))
  have hv : locals.get? "stored_length" = some (.int (Int.ofNat length.toNat)) := by simp [locals]
  have hbase : locals.get? (vaultStringName isName) = none := by cases isName <;> simp [locals, vaultStringName]
  rw [vaultStringBody_eq]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (vaultStringSourcePrefix evm isName hvalue)
  apply ExecBlock.consNormal (ExecStmt.iteFalse (show evalExpr? config {contract := contract, locals := locals} evm vaultStringWrapExpr = .ok (.bool false) from ?_) ExecBlock.nil)
  · apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    · exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (vaultStringValueEval evm locals isName hbase)))
    · have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hv
      simp only [evalExpr?, heval, evalBinaryOp?, EvalResult.bind, pure, bind]
      have hi : Int.ofNat length.toNat ≤ 64 := by
        change (length.toNat : Int) ≤ (64 : Nat)
        exact Int.ofNat_le.mpr hlen
      simp only [hi, decide_true]
  · rw [vaultStringWrapEval evm locals length hv]
    have hlt : ¬ UInt256.size - 63 ≤ length.toNat := by change ¬ 2 ^ 256 - 63 ≤ length.toNat; change length.toNat ≤ 64 at hlen; omega
    simp only [hlt, decide_false, Bool.false_and]

theorem vaultStringSourceWrapped (evm : State) (isName : Bool)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlo : UInt256.size - 63 ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat)
    (hhi : (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat ≤ UInt256.size - 32) :
    ExecTransitionBody fork config contract evm ∅ (vaultStringBody isName)
      (.returned {contract := contract, locals := vaultStringLocals (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName))}
        evm (some [.bytes ByteArray.empty])) := by
  let length := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)
  have hv : (vaultStringLocals length).get? "stored_length" = some (.int (Int.ofNat length.toNat)) := by simp [vaultStringLocals]
  rw [vaultStringBody_eq]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (vaultStringSourcePrefix evm isName hvalue)
  apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
  · rw [vaultStringWrapEval evm (vaultStringLocals length) length hv]
    dsimp only [length]
    simp only [hlo, hhi, decide_true, Bool.true_and]
  · exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by rw [evalExpr?]; rfl)))

theorem vaultStringSourceReverts (evm : State) (isName : Bool)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : 64 < (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat)
    (hwrap : ¬ (UInt256.size - 63 ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat ∧
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)).toNat ≤ UInt256.size - 32)) :
    ExecTransitionBody fork config contract evm ∅ (vaultStringBody isName) .reverted := by
  let length := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (vaultStringSlot isName)
  have hv : (vaultStringLocals length).get? "stored_length" = some (.int (Int.ofNat length.toNat)) := by simp [vaultStringLocals]
  have hguard : evalExpr? config {contract := contract, locals := vaultStringLocals length} evm vaultStringWrapExpr = .ok (.bool false) := by
    rw [vaultStringWrapEval evm (vaultStringLocals length) length hv]
    by_cases hlo : UInt256.size - 63 ≤ length.toNat
    · have hhi : ¬ length.toNat ≤ UInt256.size - 32 := fun hhi => hwrap ⟨hlo, hhi⟩
      simp only [hlo, hhi, decide_true, decide_false, Bool.true_and]
    · simp only [hlo, decide_false, Bool.false_and]
  rw [vaultStringBody_eq]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (vaultStringSourcePrefix evm isName hvalue)
  apply ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hv
  simp only [evalExpr?, heval, evalBinaryOp?, EvalResult.bind, pure, bind]
  have hi : ¬ Int.ofNat length.toNat ≤ 64 := by
    change ¬ (length.toNat : Int) ≤ (64 : Nat)
    rw [Int.ofNat_le]
    exact Nat.not_le_of_lt hlen
  simp only [hi, decide_false]

end Benchmarks.CurveVault
