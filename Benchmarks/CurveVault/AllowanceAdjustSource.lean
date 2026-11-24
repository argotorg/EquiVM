import Benchmarks.CurveVault.AllowanceStorage
import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.ApproveInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAdjustFunction (increase : Bool) : FunctionDecl :=
  if increase then contract.functions[23]! else contract.functions[24]!

def vaultAdjustDeltaName (increase : Bool) : Ident := if increase then "_add_value" else "_sub_value"

def vaultAdjustWrapped (increase : Bool) (old delta : UInt256) : UInt256 :=
  if increase then old + delta else UInt256.sub old delta

def vaultAdjustOverflow (increase : Bool) (old value : UInt256) : Bool :=
  if increase then decide (value.toNat < old.toNat) else decide (old.toNat < value.toNat)

def vaultAdjustBound (increase : Bool) : UInt256 :=
  if increase then UInt256.ofNat (UInt256.size - 1) else ⟨0⟩

def vaultAdjustValue (increase : Bool) (old delta : UInt256) : UInt256 :=
  if vaultAdjustOverflow increase old (vaultAdjustWrapped increase old delta)
  then vaultAdjustBound increase else vaultAdjustWrapped increase old delta

def vaultAdjustPrefixLocals (locals : Store) (increase : Bool) (old delta : UInt256) : Store :=
  let next := (locals.insert "cached_allowance" (.int (Int.ofNat old.toNat))).insert
    "allowance_" (.int (Int.ofNat (vaultAdjustWrapped increase old delta).toNat))
  if vaultAdjustOverflow increase old (vaultAdjustWrapped increase old delta)
  then next.insert "allowance_" (.int (Int.ofNat (vaultAdjustBound increase).toNat)) else next

theorem vaultAdjustPrefixLocals_cached (locals : Store) (increase : Bool) (old delta : UInt256) :
    (vaultAdjustPrefixLocals locals increase old delta).get? "cached_allowance" = some (.int (Int.ofNat old.toNat)) := by
  unfold vaultAdjustPrefixLocals
  split <;> simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

theorem vaultAdjustPrefixLocals_value (locals : Store) (increase : Bool) (old delta : UInt256) :
    (vaultAdjustPrefixLocals locals increase old delta).get? "allowance_" =
      some (.int (Int.ofNat (vaultAdjustValue increase old delta).toNat)) := by
  unfold vaultAdjustPrefixLocals vaultAdjustValue
  split <;> simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl

theorem vaultAdjustPrefixLocals_other (locals : Store) (increase : Bool) (old delta : UInt256)
    (name : Ident) (hc : name ≠ "cached_allowance") (ha : name ≠ "allowance_") :
    (vaultAdjustPrefixLocals locals increase old delta).get? name = locals.get? name := by
  unfold vaultAdjustPrefixLocals
  have hc' : ("cached_allowance" == name) = false := by simp [Ne.symm hc]
  have ha' : ("allowance_" == name) = false := by simp [Ne.symm ha]
  split
  · rw [store_get_ne _ _ ha', store_get_ne _ _ ha', store_get_ne _ _ hc']
  · rw [store_get_ne _ _ ha', store_get_ne _ _ hc']

theorem vaultAdjustPrefixSource (increase : Bool) (evm : State) (locals : Store)
    (spender : AccountAddress) (old delta : UInt256)
    (hbase : locals.get? "allowance" = none)
    (hspender : locals.get? "_spender" = some (.address spender))
    (hdelta : locals.get? (vaultAdjustDeltaName increase) = some (.int (Int.ofNat delta.toNat)))
    (hold : Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (vaultAllowanceSlot evm.executionEnv.source spender) = old) :
    ExecBlock fork config {contract := contract, locals := locals} evm ((vaultAdjustFunction increase).body.take 3)
      (.ok {contract := contract, locals := vaultAdjustPrefixLocals locals increase old delta} evm) := by
  have hread := vaultAllowanceEvalAt evm locals (.env .caller) (.var "_spender")
    evm.executionEnv.source spender hbase (by simp [evalExpr?, envValue, pure])
    (by rw [evalExpr?]; simp only [hspender, EvalResult.ofOption])
  rw [hold] at hread
  let locals0 := locals.insert "cached_allowance" (.int (Int.ofNat old.toNat))
  let wrapped := vaultAdjustWrapped increase old delta
  let locals1 := locals0.insert "allowance_" (.int (Int.ofNat wrapped.toNat))
  have hevalOld := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals0.get? "cached_allowance" = some (.int (Int.ofNat old.toNat)) from store_get_self _ _ _)
  have hevalDelta := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals0.get? (vaultAdjustDeltaName increase) = some (.int (Int.ofNat delta.toNat)) by
      rw [store_get_ne _ _ (by cases increase <;> decide +kernel)]; exact hdelta)
  have hcalc : evalExpr? config {contract := contract, locals := locals0} evm
      (.cast (.binary (if increase then .add else .sub) (.var "cached_allowance") (.var (vaultAdjustDeltaName increase)))
        (.elem (.int (.uint ⟨256, by decide⟩)))) = .ok (.int (Int.ofNat wrapped.toNat)) := by
    cases increase
    · exact evalExpr_castSub256 hevalOld hevalDelta
    · exact evalExpr_castAdd256 hevalOld hevalDelta
  have hevalRaw := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "allowance_" = some (.int (Int.ofNat wrapped.toNat)) from store_get_self _ _ _)
  have hevalOld1 := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show locals1.get? "cached_allowance" = some (.int (Int.ofNat old.toNat)) by
      rw [store_get_ne _ _ (by decide +kernel)]; exact store_get_self _ _ _)
  have hcond : evalExpr? config {contract := contract, locals := locals1} evm
      (.binary .lt (if increase then .var "allowance_" else .var "cached_allowance")
        (if increase then .var "cached_allowance" else .var "allowance_")) =
      .ok (.bool (vaultAdjustOverflow increase old wrapped)) := by
    cases increase <;>
      simp [evalExpr?, hevalRaw, hevalOld1, evalBinaryOp?, EvalResult.bind, pure, bind, vaultAdjustOverflow]
  have hbody : (vaultAdjustFunction increase).body.take 3 =
      [.letDecl "cached_allowance" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.storage {base := "allowance", steps := [.mindex (.env .caller), .mindex (.var "_spender")]}),
       .letDecl "allowance_" (some (.elem (.int (.uint ⟨256, by decide⟩))))
        (.cast (.binary (if increase then .add else .sub) (.var "cached_allowance") (.var (vaultAdjustDeltaName increase)))
          (.elem (.int (.uint ⟨256, by decide⟩)))),
       .ite (.binary .lt (if increase then .var "allowance_" else .var "cached_allowance")
          (if increase then .var "cached_allowance" else .var "allowance_"))
         [.assign .localVar {base := "allowance_"} (.intLit (Int.ofNat (vaultAdjustBound increase).toNat))] []] := by
    cases increase <;> rfl
  rw [hbody]
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  apply ExecBlock.consNormal (ExecStmt.letDecl hcalc)
  by_cases hc : vaultAdjustOverflow increase old wrapped = true
  · rw [hc] at hcond
    simp only [vaultAdjustPrefixLocals,
      show vaultAdjustOverflow increase old (vaultAdjustWrapped increase old delta) = true from hc, if_true]
    change ExecBlock fork _ _ _ _ (.ok {contract := contract, locals := (locals1.insert "allowance_"
      (.int (Int.ofNat (vaultAdjustBound increase).toNat)))} evm)
    refine ExecBlock.consNormal (ExecStmt.iteTrue hcond ?_) ExecBlock.nil
    exact ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (by simp [evalExpr?, pure])
      (assignLocalVarBase_ok (old := .int (Int.ofNat wrapped.toNat)) (store_get_self _ _ _))) ExecBlock.nil
  · have hc' : vaultAdjustOverflow increase old wrapped = false := by simpa using hc
    rw [hc'] at hcond
    simp only [vaultAdjustPrefixLocals,
      show vaultAdjustOverflow increase old (vaultAdjustWrapped increase old delta) = false from hc',
      Bool.false_eq_true, if_false]
    change ExecBlock fork _ _ _ _ (.ok {contract := contract, locals := locals1} evm)
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ExecBlock.nil

end Benchmarks.CurveVault
