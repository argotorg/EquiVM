import Benchmarks.EAS.Attester.MultiAttestSourceInner

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def attestOuterCond : Expr := .binary .lt (.var "i") (.var "schemaLength")

def attestOuterPost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩
    (.inRange uint256Int (.binary .add (.var "i") (.intLit 1)))]

def attestOuterBody : List Stmt :=
  [.letDecl "inputs" (some uint256Array) (.index (.var "schemaInputs") (.var "i")),
    .letDecl "inputLength" (some uint256) (.arrayLength .localVar ⟨"inputs", []⟩),
    .require (.binary .ne (.var "inputLength") (.intLit 0)),
    .assign .localVar ⟨"allocationEnd", []⟩
      (.binary .add (.var "allocationEnd") (.binary .mul (.intLit 480) (.var "inputLength"))),
    .letDecl "data" (some (.dynamicArray attestationRequestDataTy))
      (.newArray attestationRequestDataSt (.var "inputLength")),
    .for [.letDecl "j" (some uint256) (.intLit 0)]
      attestInnerCond attestInnerPost attestInnerBody,
    .assign .localVar ⟨"multiRequests", [.aindex (.var "i")]⟩
      (.tupleLit [.index (.var "schemas") (.var "i"), .var "data"])]

theorem attestSourceRowEmpty {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {rows : List Value} {i : Nat}
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hr : locals.get? "schemaInputs" = some (.array rows))
    (hrow : rows[i]? = some (.array [])) :
    ExecBlock config ⟨C, locals, imms⟩ evm attestOuterBody .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalLocalArrayIndex hr hi hrow rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayLength (values := []) ?_)) ?_
  · simp
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  have hn : ((locals.insert "inputs" (.array [])).insert "inputLength" (.int (Int.ofNat 0))).get?
      "inputLength" = some (.int (Int.ofNat 0)) := by simp
  exact evalLocalNatNeZero (cfg := config) (evm := evm)
    (solm := ⟨C, (locals.insert "inputs" (.array [])).insert "inputLength" (.int (Int.ofNat 0)),
        imms⟩)
    hn

def attestRowUntouched (name : Ident) : Prop :=
  name ≠ "inputs" ∧ name ≠ "inputLength" ∧ name ≠ "data" ∧ name ≠ "j" ∧ name ≠ "multiRequests" ∧
    name ≠ "encodedCall" ∧ name ≠ "allocationEnd"

theorem attestSourceRow {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {schemas rows requests inputs : List Value} {schema : Value} {i allocation :
        Nat} {values : Nat → UInt256}
    (hi : locals.get? "i" = some (.int (Int.ofNat i)))
    (hs : locals.get? "schemas" = some (.array schemas))
    (hr : locals.get? "schemaInputs" = some (.array rows))
    (hq : locals.get? "multiRequests" = some (.array requests))
    (hrow : rows[i]? = some (.array inputs)) (hsch : schemas[i]? = some schema)
    (hindex : i < requests.length) (hn : 0 < inputs.length) (hfit : inputs.length < UInt256.size)
    (ha : locals.get? "allocationEnd" = some (.int (Int.ofNat allocation)))
    (hsnorm : normalizeRawBoolWord? schema = .ok schema)
    (hinputs : ∀ k < inputs.length, inputs[k]? = some (.int (Int.ofNat (values k).toNat))) :
    ∃ result, ExecBlock config ⟨C, locals, imms⟩ evm attestOuterBody
      (.ok ⟨C, result, imms⟩ evm) ∧
      result.get? "multiRequests" =
        some (.array (requests.set i (.tuple [schema,
            .array (attestArrayValues values 0 inputs.length)]))) ∧
      result.get? "allocationEnd" = some (.int (Int.ofNat (allocation + 480 * inputs.length))) ∧
      ∀ name, attestRowUntouched name → result.get? name = locals.get? name := by
  let emptyPair : Value := .tuple [.address ⟨0, by decide⟩, .int 0, .bool false,
    .fixedBytes bytes32Width (List.replicate 32 0), .bytes ByteArray.empty, .int 0]
  have hdefault : defaultValue? attestationRequestDataSt = .ok emptyPair := by native_decide
  let l0 := locals.insert "inputs" (.array inputs)
  let l1 := l0.insert "inputLength" (.int (Int.ofNat inputs.length))
  let la := l1.insert "allocationEnd" (.int (Int.ofNat (allocation + 480 * inputs.length)))
  let l2 := la.insert "data" (.array (List.replicate inputs.length emptyPair))
  have h0 : ExecStmt config ⟨C, locals, imms⟩ evm
      (.letDecl "inputs" (some uint256Array) (.index (.var "schemaInputs") (.var "i")))
      (.ok ⟨C, l0, imms⟩ evm) :=
    ExecStmt.letDecl (evalLocalArrayIndex hr hi hrow rfl)
  have hu0 : l0.get? "inputs" = some (.array inputs) := by simp [l0]
  have h1 : ExecStmt config ⟨C, l0, imms⟩ evm
      (.letDecl "inputLength" (some uint256) (.arrayLength .localVar ⟨"inputs", []⟩))
      (.ok ⟨C, l1, imms⟩ evm) := ExecStmt.letDecl (evalLocalArrayLength hu0)
  have hn1 : l1.get? "inputLength" = some (.int (Int.ofNat inputs.length)) := by simp [l1]
  have h2 : ExecStmt config ⟨C, l1, imms⟩ evm
      (.require (.binary .ne (.var "inputLength") (.intLit 0))) (.ok ⟨C, l1, imms⟩ evm) :=
    ExecStmt.requireTrue (by simpa only [decide_eq_true (by omega : inputs.length ≠ 0)] using
      (evalLocalNatNeZero (cfg := config) (solm := ⟨C, l1, imms⟩) (evm := evm) hn1))
  have ha1 : l1.get? "allocationEnd" = some (.int (Int.ofNat allocation)) := by
    simpa [l1, l0, Std.HashMap.getElem?_insert] using ha
  have halloc : ExecStmt config ⟨C, l1, imms⟩ evm
      (.assign .localVar ⟨"allocationEnd", []⟩
        (.binary .add (.var "allocationEnd") (.binary .mul (.intLit 480) (.var "inputLength"))))
      (.ok ⟨C, la, imms⟩ evm) := by
    refine ExecStmt.assign (value := .int (Int.ofNat (allocation + 480 * inputs.length))) ?_ ?_
    · simp only [evalExpr?, ha1, hn1, EvalResult.ofOption, bind, pure, EvalResult.bind,
        evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    · exact assignLocalValue ha1
  have hna : la.get? "inputLength" = some (.int (Int.ofNat inputs.length)) := by
    simpa [la, Std.HashMap.getElem?_insert] using hn1
  have h3 : ExecStmt config ⟨C, la, imms⟩ evm
      (.letDecl "data" (some (.dynamicArray attestationRequestDataTy))
        (.newArray attestationRequestDataSt (.var "inputLength"))) (.ok ⟨C, l2, imms⟩ evm) :=
    ExecStmt.letDecl (evalLocalNewArray hna hdefault)
  obtain ⟨l3, hinner, hdata, hsame⟩ := attestInnerFor
    (C := C) (imms := imms) (evm := evm) (locals := l2)
    (inputs := inputs) (data := List.replicate inputs.length emptyPair) hfit
    (by simp [l2, la, l1, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l2, la, l1, l0, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [l2]) (by simp) hinputs
  have hi3 : l3.get? "i" = some (.int (Int.ofNat i)) := by
    rw [hsame "i" (by decide) (by decide) (by decide)]
    simpa [l2, la, l1, l0, Std.HashMap.getElem?_insert] using hi
  have hs3 : l3.get? "schemas" = some (.array schemas) := by
    rw [hsame "schemas" (by decide) (by decide) (by decide)]
    simpa [l2, la, l1, l0, Std.HashMap.getElem?_insert] using hs
  have hq3 : l3.get? "multiRequests" = some (.array requests) := by
    rw [hsame "multiRequests" (by decide) (by decide) (by decide)]
    simpa [l2, la, l1, l0, Std.HashMap.getElem?_insert] using hq
  have ha3 : l3.get? "allocationEnd" =
      some (.int (Int.ofNat (allocation + 480 * inputs.length))) := by
    rw [hsame "allocationEnd" (by decide) (by decide) (by decide)]
    simp [l2, la, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hvalue : evalExpr? config ⟨C, l3, imms⟩ evm
      (.tupleLit [.index (.var "schemas") (.var "i"), .var "data"]) =
        .ok (.tuple [schema, .array (attestArrayValues values 0 inputs.length)]) := by
    have he := evalLocalArrayIndex (cfg := config) (solm := ⟨C, l3, imms⟩) (evm := evm)
      hs3 hi3 hsch hsnorm
    simp only [evalExpr?, evalExprList?, he, hdata, EvalResult.ofOption, bind, EvalResult.bind,
        pure]
  refine ⟨l3.insert "multiRequests"
    (.array (requests.set i (.tuple [schema, .array (attestArrayValues values 0 inputs.length)]))),
        ?_, by simp, ?_, ?_⟩
  · exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
      (ExecBlock.consNormal halloc (ExecBlock.consNormal h3 (ExecBlock.consNormal hinner
          (ExecBlock.consNormal
        (ExecStmt.assign hvalue (assignLocalArrayIndex hq3 hi3 hindex)) ExecBlock.nil))))))
  · simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      show ("multiRequests" == "allocationEnd") = false from rfl,
      Bool.false_eq_true, if_false] using ha3
  · intro name hname
    rcases hname with ⟨hu, hn, hd, hj, hq, he, ha⟩
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_eq_false_iff_ne.mpr (Ne.symm hq), Bool.false_eq_true, if_false]
    change l3.get? name = locals.get? name
    rw [hsame name hd hj he]
    simp [l2, la, l1, l0, Std.HashMap.getElem?_insert, Ne.symm hu, Ne.symm hn, Ne.symm hd,
        Ne.symm ha]

end Benchmarks.EAS.Attester
