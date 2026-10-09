import Benchmarks.EAS.Attester.LocalArray
import Benchmarks.EAS.Attester.Spec

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def revokePairValues (uids : List Value) : List Value :=
  uids.map (fun uid ↦ .tuple [uid, .int 0])

def revokeInnerCond : Expr := .binary .lt (.var "j") (.var "uidLength")

def revokeInnerPost : List Stmt :=
  [.assign .localVar ⟨"j", []⟩
    (.inRange uint256Int (.binary .add (.var "j") (.intLit 1)))]

def revokeInnerBody : List Stmt :=
  [.assign .localVar ⟨"data", [.aindex (.var "j")]⟩
    (.tupleLit [.index (.var "uids") (.var "j"), .intLit 0])]

theorem revokeInnerRun {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {uids data : List Value} {j remaining : Nat}
    (hn : uids.length < UInt256.size) (hj : j + remaining = uids.length)
    (hi : locals.get? "j" = some (.int (Int.ofNat j)))
    (hcount : locals.get? "uidLength" = some (.int (Int.ofNat uids.length)))
    (hu : locals.get? "uids" = some (.array uids))
    (hd : locals.get? "data" = some (.array data)) (hlen : data.length = uids.length)
    (hfilled : ∀ k < j, data[k]? = (revokePairValues uids)[k]?)
    (hnorm : ∀ v ∈ uids, normalizeRawBoolWord? v = .ok v) :
    ∃ result, ExecForLoop cfg ⟨C, locals, imms⟩ evm revokeInnerCond revokeInnerPost revokeInnerBody
      (.ok ⟨C, result, imms⟩ evm) ∧
      result.get? "data" = some (.array (revokePairValues uids)) ∧
      ∀ name, name ≠ "data" → name ≠ "j" → result.get? name = locals.get? name := by
  induction remaining generalizing locals data j with
  | zero =>
      have hjn : j = uids.length := by omega
      have hdata : data = revokePairValues uids := by
        apply List.ext_getElem?
        intro k
        by_cases hk : k < j
        · exact hfilled k hk
        · have hk' : ¬ k < data.length := by omega
          have hkp : ¬ k < (revokePairValues uids).length := by
            simpa only [revokePairValues, List.length_map] using (show ¬ k < uids.length by omega)
          simp only [List.getElem?_eq_none (Nat.le_of_not_gt hk'),
            List.getElem?_eq_none (Nat.le_of_not_gt hkp)]
      refine ⟨locals, ExecForLoop.falseDone ?_, by simpa only [hdata] using hd, ?_⟩
      · simpa only [revokeInnerCond, hjn, Nat.lt_irrefl, decide_false] using
          (evalLocalNatLt (cfg := cfg) (solm := ⟨C, locals, imms⟩) (evm := evm) hi hcount)
      · intro name _ _; rfl
  | succ remaining ih =>
      have hju : j < uids.length := by omega
      have hjd : j < data.length := by omega
      let uid := uids[j]
      let value : Value := .tuple [uid, .int 0]
      let afterData := locals.insert "data" (.array (data.set j value))
      let afterStep := afterData.insert "j" (.int (Int.ofNat (j + 1)))
      have hget : uids[j]? = some uid := List.getElem?_eq_getElem hju
      have hvalue : evalExpr? cfg ⟨C, locals, imms⟩ evm
          (.tupleLit [.index (.var "uids") (.var "j"), .intLit 0]) = .ok value := by
        have hv := evalLocalArrayIndex (cfg := cfg) (solm := ⟨C, locals, imms⟩)
          (evm := evm) hu hi hget (hnorm uid (List.mem_of_getElem? hget))
        simp only [evalExpr?, evalExprList?, hv, bind, EvalResult.bind, pure, value]
      have hbody : ExecBlock cfg ⟨C, locals, imms⟩ evm revokeInnerBody
          (.ok ⟨C, afterData, imms⟩ evm) :=
        ExecBlock.consNormal (ExecStmt.assign hvalue (assignLocalArrayIndex hd hi hjd))
            ExecBlock.nil
      have hiData : afterData.get? "j" = some (.int (Int.ofNat j)) := by
        simpa [afterData, Std.HashMap.getElem?_insert] using hi
      have hpost : ExecBlock cfg ⟨C, afterData, imms⟩ evm revokeInnerPost
          (.ok ⟨C, afterStep, imms⟩ evm) := execLocalIncrement hiData (by omega)
      have hfilled' : ∀ k < j + 1, (data.set j value)[k]? = (revokePairValues uids)[k]? := by
        intro k hk
        by_cases hkj : k = j
        · subst k
          simp only [List.getElem?_set_self hjd, revokePairValues, List.getElem?_map, hget,
            Option.map_some, value]
        · rw [List.getElem?_set_ne (Ne.symm hkj)]
          exact hfilled k (by omega)
      obtain ⟨result, hrun, hdata, hsame⟩ := ih (locals := afterStep) (data := data.set j value)
        (j := j + 1) (by omega) (by simp [afterStep, Std.HashMap.getElem?_insert])
        (by simpa [afterStep, afterData, Std.HashMap.getElem?_insert] using hcount)
        (by simpa [afterStep, afterData, Std.HashMap.getElem?_insert] using hu)
        (by simp [afterStep, afterData, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
        (by simpa using hlen) hfilled'
      refine ⟨result, ExecForLoop.iterate ?_ hbody hpost hrun, hdata, ?_⟩
      · simpa only [revokeInnerCond, hju, decide_true] using
          (evalLocalNatLt (cfg := cfg) (solm := ⟨C, locals, imms⟩) (evm := evm) hi hcount)
      · intro name hdataName hjName
        rw [hsame name hdataName hjName]
        simp [afterStep, afterData, Std.HashMap.getElem?_insert, Ne.symm hdataName, Ne.symm hjName]

theorem revokeInnerFor {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {uids data : List Value}
    (hn : uids.length < UInt256.size)
    (hcount : locals.get? "uidLength" = some (.int (Int.ofNat uids.length)))
    (hu : locals.get? "uids" = some (.array uids))
    (hd : locals.get? "data" = some (.array data)) (hlen : data.length = uids.length)
    (hnorm : ∀ v ∈ uids, normalizeRawBoolWord? v = .ok v) :
    ∃ result, ExecStmt cfg ⟨C, locals, imms⟩ evm
      (.for [.letDecl "j" (some uint256) (.intLit 0)] revokeInnerCond revokeInnerPost
          revokeInnerBody)
      (.ok ⟨C, result, imms⟩ evm) ∧ result.get? "data" = some (.array (revokePairValues uids)) ∧
      ∀ name, name ≠ "data" → name ≠ "j" → result.get? name = locals.get? name := by
  obtain ⟨result, hrun, hdata, hsame⟩ := revokeInnerRun
    (cfg := cfg) (C := C) (imms := imms) (evm := evm)
    (locals := locals.insert "j" (.int 0)) (uids := uids) (data := data)
    (j := 0) (remaining := uids.length) hn (by omega) (by simp)
    (by simpa [Std.HashMap.getElem?_insert] using hcount)
    (by simpa [Std.HashMap.getElem?_insert] using hu)
    (by simpa [Std.HashMap.getElem?_insert] using hd) hlen
    (by intro k hk; omega) hnorm
  refine ⟨result, ExecStmt.for (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil) hrun,
    hdata, ?_⟩
  · simp only [evalExpr?, pure]
  · intro name hdataName hjName
    rw [hsame name hdataName hjName]
    simp [Std.HashMap.getElem?_insert, Ne.symm hjName]

end Benchmarks.EAS.Attester
