import Benchmarks.EAS.Attester.MultiRevokeSourceInner

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def revokeOuterCond : Expr := .binary .lt (.var "i") (.var "schemaLength")

def revokeOuterPost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.inRange uint256Int (.binary .add (.var "i") (.intLit 1)))]

def revokeOuterBody : List Stmt :=
  [.letDecl "uids" (some bytes32Array) (.index (.var "schemaUids") (.var "i")),
    .letDecl "uidLength" (some uint256) (.arrayLength .localVar ⟨"uids", []⟩),
    .require (.binary .ne (.var "uidLength") (.intLit 0)),
    .letDecl "data" (some (.dynamicArray revocationRequestDataTy))
      (.newArray revocationRequestDataSt (.var "uidLength")),
    .for [.letDecl "j" (some uint256) (.intLit 0)]
      revokeInnerCond revokeInnerPost revokeInnerBody,
    .assign .localVar ⟨"multiRequests", [.aindex (.var "i")]⟩
      (.tupleLit [.index (.var "schemas") (.var "i"), .var "data"])]

theorem revokeSourceRowEmpty {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {rows : List Value} {i : Nat}
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hr : locals.get? "schemaUids" = some (.array rows))
    (hrow : rows[i]? = some (.array [])) :
    ExecBlock cfg ⟨C, locals, imms⟩ evm revokeOuterBody .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalLocalArrayIndex hr hi hrow rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (values := []) ?_)) ?_
  · simp
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have hn : ((locals.insert "uids" (.array [])).insert "uidLength" (.int (Int.ofNat 0))).get?
      "uidLength" = some (.int (Int.ofNat 0)) := by simp
  exact evalLocalNatNeZero (cfg := cfg) (evm := evm)
    (solm := ⟨C, (locals.insert "uids" (.array [])).insert "uidLength" (.int (Int.ofNat 0)), imms⟩)
    hn

def revokeRowUntouched (name : Ident) : Prop :=
  name ≠ "uids" ∧ name ≠ "uidLength" ∧ name ≠ "data" ∧ name ≠ "j" ∧ name ≠ "multiRequests"

theorem revokeSourceRow {cfg : Config} {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests uids : List Value} {schema : Value} {i : Nat}
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaUids" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (hrow : rows[i]? = some (.array uids)) (hsch : schemas[i]? = some schema)
    (hindex : i < requests.length) (hn : 0 < uids.length) (hfit : uids.length < UInt256.size)
    (hsnorm : normalizeRawBoolWord? schema = .ok schema)
    (hnorm : ∀ v ∈ uids, normalizeRawBoolWord? v = .ok v) :
    ∃ result, ExecBlock cfg ⟨C, locals, imms⟩ evm revokeOuterBody
      (.ok ⟨C, result, imms⟩ evm) ∧
      result.get? "multiRequests" =
        some (.array (requests.set i (.tuple [schema, .array (revokePairValues uids)]))) ∧
      ∀ name, revokeRowUntouched name → result.get? name = locals.get? name := by
  let emptyPair : Value := .tuple [.fixedBytes bytes32Width (List.replicate 32 0), .int 0]
  have hdefault : defaultValue? revocationRequestDataSt = .ok emptyPair := by native_decide
  let l0 := locals.insert "uids" (.array uids)
  let l1 := l0.insert "uidLength" (.int (Int.ofNat uids.length))
  let l2 := l1.insert "data" (.array (List.replicate uids.length emptyPair))
  have h0 : ExecStmt cfg ⟨C, locals, imms⟩ evm
      (.letDecl "uids" (some bytes32Array) (.index (.var "schemaUids") (.var "i")))
      (.ok ⟨C, l0, imms⟩ evm) :=
    ExecStmt.letDecl (evalLocalArrayIndex hr hi hrow rfl)
  have hu0 : l0.get? "uids" = some (.array uids) := by simp [l0]
  have h1 : ExecStmt cfg ⟨C, l0, imms⟩ evm
      (.letDecl "uidLength" (some uint256) (.arrayLength .localVar ⟨"uids", []⟩))
      (.ok ⟨C, l1, imms⟩ evm) := ExecStmt.letDecl (evalLocalArrayLength hu0)
  have hn1 : l1.get? "uidLength" = some (.int (Int.ofNat uids.length)) := by simp [l1]
  have h2 : ExecStmt cfg ⟨C, l1, imms⟩ evm
      (.require (.binary .ne (.var "uidLength") (.intLit 0))) (.ok ⟨C, l1, imms⟩ evm) :=
    ExecStmt.requireTrue (by simpa only [decide_eq_true (by omega : uids.length ≠ 0)] using
      (evalLocalNatNeZero (cfg := cfg) (solm := ⟨C, l1, imms⟩) (evm := evm) hn1))
  have h3 : ExecStmt cfg ⟨C, l1, imms⟩ evm
      (.letDecl "data" (some (.dynamicArray revocationRequestDataTy))
        (.newArray revocationRequestDataSt (.var "uidLength"))) (.ok ⟨C, l2, imms⟩ evm) :=
    ExecStmt.letDecl (evalLocalNewArray hn1 hdefault)
  obtain ⟨l3, hinner, hdata, hsame⟩ := revokeInnerFor
    (cfg := cfg) (C := C) (imms := imms) (evm := evm) (locals := l2)
    (uids := uids) (data := List.replicate uids.length emptyPair) hfit
    (by simp [l2, l1, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l2, l1, l0, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l2]) (by simp) hnorm
  have hi3 : l3.get? "i" = some (.int (Int.ofNat i)) := by
    rw [hsame "i" (by decide) (by decide)]
    simpa [l2, l1, l0, Std.HashMap.getElem?_insert] using hi
  have hs3 : l3.get? "schemas" = some (.array schemas) := by
    rw [hsame "schemas" (by decide) (by decide)]
    simpa [l2, l1, l0, Std.HashMap.getElem?_insert] using hs
  have hq3 : l3.get? "multiRequests" = some (.array requests) := by
    rw [hsame "multiRequests" (by decide) (by decide)]
    simpa [l2, l1, l0, Std.HashMap.getElem?_insert] using hq
  have hvalue : evalExpr? cfg ⟨C, l3, imms⟩ evm
      (.tupleLit [.index (.var "schemas") (.var "i"), .var "data"]) =
        .ok (.tuple [schema, .array (revokePairValues uids)]) := by
    have he := evalLocalArrayIndex (cfg := cfg) (solm := ⟨C, l3, imms⟩) (evm := evm)
      hs3 hi3 hsch hsnorm
    simp only [evalExpr?, evalExprList?, he, hdata, EvalResult.ofOption, bind, EvalResult.bind,
        pure]
  refine ⟨l3.insert "multiRequests"
    (.array (requests.set i (.tuple [schema, .array (revokePairValues uids)]))), ?_, by simp, ?_⟩
  · exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
      (ExecBlock.consNormal h3 (ExecBlock.consNormal hinner (ExecBlock.consNormal
        (ExecStmt.assign hvalue (assignLocalArrayIndex hq3 hi3 hindex)) ExecBlock.nil)))))
  · intro name hname
    rcases hname with ⟨hu, hn, hd, hj, hq⟩
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_eq_false_iff_ne.mpr (Ne.symm hq), Bool.false_eq_true, if_false]
    change l3.get? name = locals.get? name
    rw [hsame name hd hj]
    simp [l2, l1, l0, Std.HashMap.getElem?_insert, Ne.symm hu, Ne.symm hn, Ne.symm hd]

end Benchmarks.EAS.Attester
