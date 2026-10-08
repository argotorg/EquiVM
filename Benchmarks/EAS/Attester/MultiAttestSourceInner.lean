import Benchmarks.EAS.Attester.LocalArray
import Benchmarks.EAS.Attester.AttestSource
import Benchmarks.EAS.Attester.AttestCellABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def attestInnerCond : Expr := .binary .lt (.var "j") (.var "inputLength")

def attestInnerPost : List Stmt :=
  [.assign .localVar ⟨"j", []⟩
    (.inRange uint256Int (.binary .add (.var "j") (.intLit 1)))]

def attestCellExpr : Expr :=
  .tupleLit [.cast (.intLit 0) (.elem .address), .intLit 0, .boolLit true,
    .fixedBytesLit abiBytes32Width (List.replicate 32 0),
    .bytesSlice (.var "encodedCall") (.intLit 4) (.intLit 36), .intLit 0]

def attestInnerBody : List Stmt :=
  [.letDecl "encodedCall" (some bytesTy)
    (.abiEncodeCall "__abi_encode_uint256" [.index (.var "inputs") (.var "j")]),
    .assign .localVar ⟨"data", [.aindex (.var "j")]⟩ attestCellExpr]

theorem evalAttestCellExpr {C : ContractDecl} {imms locals : Store} {evm : State}
    {input : UInt256}
    (henc : locals.get? "encodedCall" = some (.bytes (abiEncodeUint256Selector ++
        input.toByteArray))) :
    evalExpr? config ⟨C, locals, imms⟩ evm attestCellExpr = .ok (attestCellValue input) := by
  have haddr : castValue? (.int 0) (.elem .address) = some (.address ⟨0, by decide⟩) :=
    by native_decide
  have hzero : wordBytes32Value (⟨0⟩ : UInt256) =
      .fixedBytes abiBytes32Width (List.replicate 32 0) := by native_decide
  change locals["encodedCall"]? = _ at henc
  simp [attestCellExpr, evalExpr?, evalExprList?, henc, haddr, hzero, attestCellValue,
    EvalResult.ofOption, bind, pure, EvalResult.bind, sliceBytes?, ByteArray.size_append,
    toByteArray_size, show abiEncodeUint256Selector.size = 4 from rfl, encodedInput_extract]

theorem attestInnerRun {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {inputs data : List Value} {values : Nat → UInt256} {j remaining : Nat}
    (hn : inputs.length < UInt256.size) (hj : j + remaining = inputs.length)
    (hi : locals.get? "j" = some (.int (Int.ofNat j)))
    (hcount : locals.get? "inputLength" = some (.int (Int.ofNat inputs.length)))
    (hu : locals.get? "inputs" = some (.array inputs))
    (hd : locals.get? "data" = some (.array data)) (hlen : data.length = inputs.length)
    (hfilled : ∀ k < j, data[k]? = (attestArrayValues values 0 inputs.length)[k]?)
    (hinputs : ∀ k < inputs.length, inputs[k]? = some (.int (Int.ofNat (values k).toNat))) :
    ∃ result, ExecForLoop config ⟨C, locals, imms⟩ evm attestInnerCond attestInnerPost
        attestInnerBody
      (.ok ⟨C, result, imms⟩ evm) ∧
      result.get? "data" = some (.array (attestArrayValues values 0 inputs.length)) ∧
      ∀ name, name ≠ "data" → name ≠ "j" → name ≠ "encodedCall" →
        result.get? name = locals.get? name := by
  induction remaining generalizing locals data j with
  | zero =>
      have hjn : j = inputs.length := by omega
      have hdata : data = attestArrayValues values 0 inputs.length := by
        apply List.ext_getElem?
        intro k
        by_cases hk : k < j
        · exact hfilled k hk
        · have hk' : ¬ k < data.length := by omega
          have hkp : ¬ k < (attestArrayValues values 0 inputs.length).length := by
            rw [attestArrayValues_length]; omega
          simp only [List.getElem?_eq_none (Nat.le_of_not_gt hk'),
            List.getElem?_eq_none (Nat.le_of_not_gt hkp)]
      refine ⟨locals, ExecForLoop.falseDone ?_, by simpa only [hdata] using hd, ?_⟩
      · simpa only [attestInnerCond, hjn, Nat.lt_irrefl, decide_false] using
          (evalLocalNatLt (cfg := config) (solm := ⟨C, locals, imms⟩) (evm := evm) hi hcount)
      · intro name _ _ _; rfl
  | succ remaining ih =>
      have hju : j < inputs.length := by omega
      have hjd : j < data.length := by omega
      let encoded := locals.insert "encodedCall"
        (.bytes (abiEncodeUint256Selector ++ (values j).toByteArray))
      let value := attestCellValue (values j)
      let afterData := encoded.insert "data" (.array (data.set j value))
      let afterStep := afterData.insert "j" (.int (Int.ofNat (j + 1)))
      have hencode : evalExpr? config ⟨C, locals, imms⟩ evm
          (.abiEncodeCall "__abi_encode_uint256" [.index (.var "inputs") (.var "j")]) =
          .ok (.bytes (abiEncodeUint256Selector ++ (values j).toByteArray)) := by
        have hv := evalLocalArrayIndex (cfg := config) (solm := ⟨C, locals, imms⟩)
          (evm := evm) hu hi (hinputs j hju) (by rfl)
        simp only [evalExpr?, evalExprs?, evalExprList?, hv, bind, EvalResult.bind, pure,
          encodeInput, EvalResult.ofOption]
      have hbody : ExecBlock config ⟨C, locals, imms⟩ evm attestInnerBody
          (.ok ⟨C, afterData, imms⟩ evm) := by
        refine ExecBlock.consNormal (ExecStmt.letDecl hencode) ?_
        refine ExecBlock.consNormal
          (ExecStmt.assign (evalAttestCellExpr (input := values j) ?_) ?_) ExecBlock.nil
        · simp [encoded, Std.HashMap.getElem?_insert]
        · apply assignLocalArrayIndex (by simpa [encoded, Std.HashMap.getElem?_insert] using hd)
            (by simpa [encoded, Std.HashMap.getElem?_insert] using hi) hjd
      have hiData : afterData.get? "j" = some (.int (Int.ofNat j)) := by
        simpa [afterData, encoded, Std.HashMap.getElem?_insert] using hi
      have hpost : ExecBlock config ⟨C, afterData, imms⟩ evm attestInnerPost
          (.ok ⟨C, afterStep, imms⟩ evm) := execLocalIncrement hiData (by omega)
      have hfilled' : ∀ k < j + 1,
          (data.set j value)[k]? = (attestArrayValues values 0 inputs.length)[k]? := by
        intro k hk
        by_cases hkj : k = j
        · subst k
          rw [List.getElem?_set_self hjd, attestArrayValues_getElem _ _ _ _ hju]
          simp only [Nat.zero_add, value]
        · rw [List.getElem?_set_ne (Ne.symm hkj)]
          exact hfilled k (by omega)
      obtain ⟨result, hrun, hdata, hsame⟩ := ih (locals := afterStep) (data := data.set j value)
        (j := j + 1) (by omega) (by simp [afterStep, Std.HashMap.getElem?_insert])
        (by simpa [afterStep, afterData, encoded, Std.HashMap.getElem?_insert] using hcount)
        (by simpa [afterStep, afterData, encoded, Std.HashMap.getElem?_insert] using hu)
        (by simp [afterStep, afterData, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
        (by simpa using hlen) hfilled'
      refine ⟨result, ExecForLoop.iterate ?_ hbody hpost hrun, hdata, ?_⟩
      · simpa only [attestInnerCond, hju, decide_true] using
          (evalLocalNatLt (cfg := config) (solm := ⟨C, locals, imms⟩) (evm := evm) hi hcount)
      · intro name hdataName hjName hencName
        rw [hsame name hdataName hjName hencName]
        simp [afterStep, afterData, encoded, Std.HashMap.getElem?_insert,
          Ne.symm hdataName, Ne.symm hjName, Ne.symm hencName]

theorem attestInnerFor {C : ContractDecl} {imms : Store} {evm : State}
    {locals : Store} {inputs data : List Value} {values : Nat → UInt256}
    (hn : inputs.length < UInt256.size)
    (hcount : locals.get? "inputLength" = some (.int (Int.ofNat inputs.length)))
    (hu : locals.get? "inputs" = some (.array inputs))
    (hd : locals.get? "data" = some (.array data)) (hlen : data.length = inputs.length)
    (hinputs : ∀ k < inputs.length, inputs[k]? = some (.int (Int.ofNat (values k).toNat))) :
    ∃ result, ExecStmt config ⟨C, locals, imms⟩ evm
      (.for [.letDecl "j" (some uint256) (.intLit 0)] attestInnerCond attestInnerPost
          attestInnerBody)
      (.ok ⟨C, result, imms⟩ evm) ∧
      result.get? "data" = some (.array (attestArrayValues values 0 inputs.length)) ∧
      ∀ name, name ≠ "data" → name ≠ "j" → name ≠ "encodedCall" →
        result.get? name = locals.get? name := by
  obtain ⟨result, hrun, hdata, hsame⟩ := attestInnerRun
    (C := C) (imms := imms) (evm := evm)
    (locals := locals.insert "j" (.int 0)) (inputs := inputs) (data := data)
    (j := 0) (remaining := inputs.length) hn (by omega) (by simp)
    (by simpa [Std.HashMap.getElem?_insert] using hcount)
    (by simpa [Std.HashMap.getElem?_insert] using hu)
    (by simpa [Std.HashMap.getElem?_insert] using hd) hlen (by intro k hk; omega) hinputs
  refine ⟨result, ExecStmt.for (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil) hrun,
    hdata, ?_⟩
  · simp only [evalExpr?, pure]
  · intro name hdataName hjName hencName
    rw [hsame name hdataName hjName hencName]
    simp [Std.HashMap.getElem?_insert, Ne.symm hjName]

end Benchmarks.EAS.Attester
