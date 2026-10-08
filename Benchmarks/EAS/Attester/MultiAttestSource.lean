import Benchmarks.EAS.Attester.MultiAttestAllocation
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def multiAttestLocals (schemas rows : List Value) : Store :=
  ((∅ : Store).insert "schemas" (.array schemas)).insert "schemaInputs" (.array rows)

theorem multiAttestDecode_some {cd : ByteArray} {schemas rows : List Value}
    (hd : decodeArrays? uint256 cd = some (.array schemas, .array rows)) :
    decodeCalldataWithMode config.abiDecodeMode (multiAttestTransition.params.map Param.name)
      (transitionSignature multiAttestTransition).paramTypes cd =
        some (multiAttestLocals schemas rows) := by
  simpa only [hd, Option.map_some, multiAttestLocals] using
    decodeCalldata_arrays_eq uint256 "schemas" "schemaInputs" cd

theorem multiAttestDecode_none {cd : ByteArray} (hd : decodeArrays? uint256 cd = none) :
    decodeCalldataWithMode config.abiDecodeMode (multiAttestTransition.params.map Param.name)
      (transitionSignature multiAttestTransition).paramTypes cd = none := by
  simpa only [hd, Option.map_none] using decodeCalldata_arrays_eq uint256 "schemas" "schemaInputs"
      cd

def multiAttestShapeGuard : Expr :=
  .binary .and (.binary .ne (.var "schemaLength") (.intLit 0))
    (.binary .eq (.var "schemaLength") (.arrayLength .localVar ⟨"schemaInputs", []⟩))

theorem multiAttestShapeGuard_eval {cfg solm evm} {n : Nat} {rows : List Value}
    (hn : solm.locals.get? "schemaLength" = some (.int (Int.ofNat n)))
    (hr : solm.locals.get? "schemaInputs" = some (.array rows)) :
    evalExpr? cfg solm evm multiAttestShapeGuard =
      .ok (.bool (decide (0 < n ∧ rows.length = n))) := by
  rw [multiAttestShapeGuard, evalExpr?, evalLocalNatNeZero hn]
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

theorem multiAttestSourcePrelude {imms : Store} {evm : State} {schemas rows : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config ⟨contract, multiAttestLocals schemas rows, imms⟩ evm
      (multiAttestTransition.body.take 2)
      (.ok ⟨contract, (multiAttestLocals schemas rows).insert "schemaLength"
        (.int (Int.ofNat schemas.length)), imms⟩ evm) := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hvalue)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (values := schemas) ?_))
    ExecBlock.nil
  simp [multiAttestLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem multiAttestSourceBadShape {imms : Store} {evm : State} {schemas rows : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hbad : ¬ (0 < schemas.length ∧ rows.length = schemas.length)) :
    ExecTransitionBody config contract evm (multiAttestLocals schemas rows)
      multiAttestTransition.body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 multiAttestTransition.body]
  apply execBlock_append (multiAttestSourcePrelude hvalue)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have he := multiAttestShapeGuard_eval (cfg := config) (evm := evm)
    (solm := ⟨contract, (multiAttestLocals schemas rows).insert "schemaLength"
      (.int (Int.ofNat schemas.length)), imms⟩) (n := schemas.length) (rows := rows)
    (by simp) (by simp [multiAttestLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  simpa only [decide_eq_false hbad] using he

set_option maxHeartbeats 1000000 in
theorem multiAttestSourceBuild {imms : Store} {evm : State} {cd : ByteArray}
    {schemas rows : List Value} {eas : EVM.Address}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hget : imms.get? "_eas" = some (.address eas))
    (hd : decodeArrays? uint256 cd = some (.array schemas, .array rows))
    (hshape : BatchShape cd) (hsel : cd.extract 0 4 = attesterMultiAttestSelBytes) :
    (¬ BatchRowsValid cd ∧ ExecTransitionBody config contract evm (multiAttestLocals schemas rows)
      multiAttestTransition.body .reverted imms) ∨
    (BatchRowsValid cd ∧ ∃ locals,
      ExecBlock config ⟨contract, multiAttestLocals schemas rows, imms⟩ evm
        (multiAttestTransition.body.take 7) (.ok ⟨contract, locals, imms⟩ evm) ∧
      locals.get? "eas" = some (.address eas) ∧
      locals.get? "multiRequests" = some (multiAttestRequests cd) ∧
      locals.get? "allocationEnd" = some (.int (Int.ofNat (multiAttestBuiltFree cd)))) := by
  obtain ⟨schemas', rows', _end, hv, hslen, hrlen, _hdecoded⟩ := decodeArrays_first_facts hd
  cases (Prod.mk.inj hv).1
  cases (Prod.mk.inj hv).2
  have hcap := uint64Bound_of_isZero_gt (decodeArrays_some_checks hd).first.length
  change arrayCount cd 4 ≤ solcMaxU64 at hcap
  have hn : arrayCount cd 4 < UInt256.size := by
    norm_num only [solcMaxU64, UInt256.size] at hcap ⊢
    omega
  let expected := attestRequestsValues (multiAttestSchemas cd) (multiAttestCounts cd)
    (multiAttestValues cd) 0 (arrayCount cd 4)
  let emptyRequest : Value := .tuple [.fixedBytes bytes32Width (List.replicate 32 0), .array []]
  have hdefault : defaultValue? multiAttestationRequestSt = .ok emptyRequest := by native_decide
  let l0 := (multiAttestLocals schemas rows).insert "schemaLength" (.int (Int.ofNat schemas.length))
  let l1 := l0.insert "multiRequests" (.array (List.replicate schemas.length emptyRequest))
  have hn0 : l0.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by simp [l0]
  have hr0 : l0.get? "schemaInputs" = some (.array rows) := by
    simp [l0, multiAttestLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hguard : evalExpr? config ⟨contract, l0, imms⟩ evm multiAttestShapeGuard =
      .ok (.bool true) := by
    have he := multiAttestShapeGuard_eval (cfg := config) (evm := evm)
      (solm := ⟨contract, l0, imms⟩) hn0 hr0
    rw [hslen, hrlen, decide_eq_true
      (show 0 < arrayCount cd 4 ∧ arrayCount cd 36 = arrayCount cd 4 from hshape)] at he
    exact he
  have hnew : ExecStmt config ⟨contract, l0, imms⟩ evm
      (.letDecl "multiRequests" (some multiAttestationRequestArrayTy)
        (.newArray multiAttestationRequestSt (.var "schemaLength")))
      (.ok ⟨contract, l1, imms⟩ evm) := ExecStmt.letDecl (evalLocalNewArray hn0 hdefault)
  let la := l1.insert "allocationEnd" (.int (Int.ofNat (160 + 192 * schemas.length)))
  have hn1 : l1.get? "schemaLength" = some (.int (Int.ofNat schemas.length)) := by
    simpa [l1, Std.HashMap.getElem?_insert] using hn0
  have halloc : ExecStmt config ⟨contract, l1, imms⟩ evm
      (.letDecl "allocationEnd" (some uint256)
        (.binary .add (.intLit 160) (.binary .mul (.intLit 192) (.var "schemaLength"))))
      (.ok ⟨contract, la, imms⟩ evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, hn1, EvalResult.ofOption, bind, pure, EvalResult.bind,
      evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hp : ExecBlock config ⟨contract, multiAttestLocals schemas rows, imms⟩ evm
      (multiAttestTransition.body.take 5) (.ok ⟨contract, la, imms⟩ evm) := by
    exact execBlock_append (multiAttestSourcePrelude hvalue)
      (ExecBlock.consNormal (ExecStmt.requireTrue hguard) (ExecBlock.consNormal hnew
          (ExecBlock.consNormal halloc ExecBlock.nil)))
  have hloop := attestOuterFor (C := contract) (imms := imms) (evm := evm)
    (locals := la) (schemas := schemas) (rows := rows) (expected := expected)
    (requests := List.replicate schemas.length emptyRequest) (n := arrayCount cd 4)
    (allocation := 160 + 192 * schemas.length)
    (counts := multiAttestCounts cd) (values := multiAttestValues cd) hn
    (by simpa only [la, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      show ("allocationEnd" == "schemaLength") = false from rfl, Bool.false_eq_true,
      if_false, hslen] using hn1)
    (by simp [la, l1, l0, multiAttestLocals, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert])
    (by simp [la, l1, l0, multiAttestLocals, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert])
    (by simp [la, l1, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [la]) (by simpa using hslen) (attestRequestsValues_length _ _ _ _ _)
    (multiAttestDecodedViews hd hshape hsel)
  rcases hloop with ⟨⟨i, hi, hempty⟩, hloop⟩ | ⟨hnonempty, result, hloop, hrequests, hallocation,
      _hsame⟩
  · refine .inl ⟨?_, ExecFuncBody.execBlockRevert ?_⟩
    · intro hvalid
      exact (multiAttestDecoded_nonempty_iff hd hshape).mp hvalid i hi hempty
    · rw [← List.take_append_drop 5 multiAttestTransition.body]
      exact execBlock_append hp (ExecBlock.consRevert hloop)
  · refine .inr ⟨(multiAttestDecoded_nonempty_iff hd hshape).mpr hnonempty,
      result.insert "eas" (.address eas), ?_, by simp, ?_, ?_⟩
    · exact execBlock_append hp (ExecBlock.consNormal hloop
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, hget,
            EvalResult.ofOption]))
          ExecBlock.nil))
    · simpa [multiAttestRequests, expected, Std.HashMap.getElem?_insert] using hrequests
    · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        show ("eas" == "allocationEnd") = false from rfl, Bool.false_eq_true, if_false,
        hslen, multiAttestBuiltFree_eq_allocation] using hallocation

theorem multiAttestSourceSuffix {imms locals : Store} {evm : State} {schemas rows : List Value}
    {result : ExecResult}
    (hp : ExecBlock config ⟨contract, multiAttestLocals schemas rows, imms⟩ evm
      (multiAttestTransition.body.take 7) (.ok ⟨contract, locals, imms⟩ evm))
    (hs : ExecBlock config ⟨contract, locals, imms⟩ evm
      (multiAttestTransition.body.drop 7) result) :
    ExecBlock config ⟨contract, multiAttestLocals schemas rows, imms⟩ evm
      multiAttestTransition.body result := by
  rw [← List.take_append_drop 7 multiAttestTransition.body]
  exact execBlock_append hp hs

end Benchmarks.EAS.Attester
