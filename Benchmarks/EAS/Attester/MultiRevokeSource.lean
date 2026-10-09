import Benchmarks.EAS.Attester.MultiRevokeSourceABI
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def multiRevokeLocals (schemas rows : List Value) : Store :=
  ((∅ : Store).insert "schemas" (.array schemas)).insert "schemaUids" (.array rows)

theorem multiRevokeDecode_some {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? bytes32 cd = some (.array schemas, .array rows)) :
    decodeCalldataWithMode config.abiDecodeMode (multiRevokeTransition.params.map Param.name)
      (transitionSignature multiRevokeTransition).paramTypes cd =
        some (multiRevokeLocals schemas rows) := by
  simpa only [hd, Option.map_some, multiRevokeLocals] using
    decodeCalldata_arrays_eq bytes32 "schemas" "schemaUids" cd

theorem multiRevokeDecode_none {cd : ByteArray} (hd : decodeArrays? bytes32 cd = none) :
    decodeCalldataWithMode config.abiDecodeMode (multiRevokeTransition.params.map Param.name)
      (transitionSignature multiRevokeTransition).paramTypes cd = none := by
  simpa only [hd, Option.map_none] using decodeCalldata_arrays_eq bytes32 "schemas" "schemaUids" cd

def multiRevokeShapeGuard : Expr :=
  .binary .and (.binary .ne (.var "schemaLength") (.intLit 0))
    (.binary .eq (.var "schemaLength") (.arrayLength .localVar ⟨"schemaUids", []⟩))

theorem multiRevokeShapeGuard_eval {cfg solm evm} {n : Nat} {rows : List Value}
    (hn : solm.locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hr : solm.locals.get? "schemaUids" = some (.array rows)) :
    evalExpr? cfg solm evm multiRevokeShapeGuard =
      .ok (.bool (decide (0 < n ∧ rows.length = n))) := by
  rw [multiRevokeShapeGuard, evalExpr?, evalLocalNatNeZero hn]
  simp only [bind, EvalResult.bind]
  by_cases hz : n = 0
  · subst n
    simp only [Nat.lt_irrefl, false_and, ne_eq, not_true_eq_false, decide_false, pure]
  · rw [decide_eq_true hz]
    simp only [evalExpr?, hn, hr, readLocalPath?, EvalResult.ofOption, bind, EvalResult.bind,
      pure, evalBinaryOp?]
    rw [beq_eq_decide]
    simp only [Value.int.injEq, Int.ofNat_eq_natCast, Nat.cast_inj,
      show 0 < n by omega, true_and, eq_comm]

theorem multiRevokeSourcePrelude {imms : Store} {evm : State} {schemas rows : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config ⟨contract, multiRevokeLocals schemas rows, imms⟩ evm
      (multiRevokeTransition.body.take 2)
      (.ok ⟨contract, (multiRevokeLocals schemas rows).insert "schemaLength"
        (.int (Int.ofNat schemas.length)), imms⟩ evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (values := schemas) ?_))
    ExecBlock.nil
  simp [multiRevokeLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem multiRevokeSourceBadShape {imms : Store} {evm : State} {schemas rows : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hbad : ¬ (0 < schemas.length ∧ rows.length = schemas.length)) :
    ExecTransitionBody config contract evm (multiRevokeLocals schemas rows)
      multiRevokeTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 multiRevokeTransition.body]
  apply execBlock_append (multiRevokeSourcePrelude hvalue)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have he := multiRevokeShapeGuard_eval (cfg := config) (evm := evm)
    (solm := ⟨contract, (multiRevokeLocals schemas rows).insert "schemaLength"
      (.int (Int.ofNat schemas.length)), imms⟩) (n := schemas.length) (rows := rows)
    (by simp) (by simp [multiRevokeLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  simpa only [decide_eq_false hbad] using he

set_option maxHeartbeats 1000000 in
theorem multiRevokeSourceBuild {imms : Store} {evm : State} {cd : ByteArray}
    {schemas rows : List Value} {eas : EVM.Address}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hd : decodeArrays? bytes32 cd = some (.array schemas, .array rows))
    (hshape : BatchShape cd) (hsel : cd.extract 0 4 = attesterMultiRevokeSelBytes) :
    (¬ BatchRowsValid cd ∧ ExecTransitionBody config contract evm (multiRevokeLocals schemas rows)
      multiRevokeTransition.body .reverted imms) ∨
    (BatchRowsValid cd ∧ ∃ locals,
      ExecBlock config ⟨contract, multiRevokeLocals schemas rows, imms⟩ evm
        (multiRevokeTransition.body.take 6) (.ok ⟨contract, locals, imms⟩ evm) ∧
      locals.get? "eas" = some (.address eas) ∧
      locals.get? "multiRequests" = some (multiRevokeRequests cd)) := by
  obtain ⟨schemas', rows', _end, hv, hslen, hrlen, _hdecoded⟩ := decodeArrays_first_facts hd
  cases (Prod.mk.inj hv).1
  cases (Prod.mk.inj hv).2
  have hcap := uint64Bound_of_isZero_gt (decodeArrays_some_checks hd).first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hcap
  have hn : arrayCount cd 4 < UInt256.size := by
    norm_num only [solcMaxU64, UInt256.size] at hcap ⊢
    omega
  let expected := pairRequestsValues (multiRevokeSchemas cd) (multiRevokeCounts cd)
    (multiRevokeValues cd) 0 (arrayCount cd 4)
  let emptyRequest : Value := .tuple [.fixedBytes bytes32Width (List.replicate 32 0), .array []]
  have hdefault : defaultValue? multiRevocationRequestSt = .ok emptyRequest := by native_decide
  let l0 := (multiRevokeLocals schemas rows).insert "schemaLength" (.int (Int.ofNat schemas.length))
  let l1 := l0.insert "multiRequests" (.array (List.replicate schemas.length emptyRequest))
  have hn0 : l0.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by simp [l0]
  have hr0 : l0.get? "schemaUids" = some (.array rows) := by
    simp [l0, multiRevokeLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hguard : evalExpr? config ⟨contract, l0, imms⟩ evm multiRevokeShapeGuard =
      .ok (.bool true) := by
    have he := multiRevokeShapeGuard_eval (cfg := config) (evm := evm)
      (solm := ⟨contract, l0, imms⟩) hn0 hr0
    rw [hslen, hrlen, decide_eq_true
      (show 0 < arrayCount cd 4 ∧ arrayCount cd 36 = arrayCount cd 4 from hshape)] at he
    exact he
  have hnew : ExecStmt config ⟨contract, l0, imms⟩ evm
      (.letDecl "multiRequests" (some multiRevocationRequestArrayTy)
        (.newArray multiRevocationRequestSt (.var "schemaLength")))
      (.ok ⟨contract, l1, imms⟩ evm) := ExecStmt.letDecl (evalLocalNewArray hn0 hdefault)
  have hp : ExecBlock config ⟨contract, multiRevokeLocals schemas rows, imms⟩ evm
      (multiRevokeTransition.body.take 4) (.ok ⟨contract, l1, imms⟩ evm) := by
    exact execBlock_append (multiRevokeSourcePrelude hvalue)
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard) (ExecBlock.consNormal hnew ExecBlock.nil))
  have hloop := revokeOuterFor (cfg := config) (C := contract) (imms := imms) (evm := evm)
    (locals := l1) (schemas := schemas) (rows := rows) (expected := expected)
    (requests := List.replicate schemas.length emptyRequest) (n := arrayCount cd 4) hn
    (by simpa [l1, l0, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hslen])
    (by simp [l1, l0, multiRevokeLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l1, l0, multiRevokeLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l1]) (by simpa using hslen) (pairRequestsValues_length _ _ _ _ _)
    (multiRevokeDecodedViews hd hshape hsel)
  rcases hloop with ⟨⟨i, hi, hempty⟩, hloop⟩ | ⟨hnonempty, result, hloop, hrequests, _hsame⟩
  · refine .inl ⟨?_, ExecFuncBody.execBlockRevert ?_⟩
    · intro hvalid
      exact (multiRevokeDecoded_nonempty_iff hd hshape).mp hvalid i hi hempty
    · rw [← List.take_append_drop 4 multiRevokeTransition.body]
      exact execBlock_append hp (ExecBlock.consRevert hloop)
  · refine .inr ⟨(multiRevokeDecoded_nonempty_iff hd hshape).mpr hnonempty,
      result.insert "eas" (.address eas), ?_, by simp, ?_⟩
    · exact execBlock_append hp (ExecBlock.consNormal hloop
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, hget,
            EvalResult.ofOption]))
          ExecBlock.nil))
    · simpa [multiRevokeRequests, expected, Std.HashMap.getElem?_insert] using hrequests

theorem multiRevokeSourceSuffix {imms locals : Store} {evm : State} {schemas rows : List Value}
    {result : ExecResult}
    (hp : ExecBlock config ⟨contract, multiRevokeLocals schemas rows, imms⟩ evm
      (multiRevokeTransition.body.take 6) (.ok ⟨contract, locals, imms⟩ evm))
    (hs : ExecBlock config ⟨contract, locals, imms⟩ evm
      (multiRevokeTransition.body.drop 6) result) :
    ExecBlock config ⟨contract, multiRevokeLocals schemas rows, imms⟩ evm
      multiRevokeTransition.body result := by
  rw [← List.take_append_drop 6 multiRevokeTransition.body]
  exact execBlock_append hp hs

end Benchmarks.EAS.Attester
