import Benchmarks.UniswapV3.Pool.SourceReverts
import Benchmarks.UniswapV3.Pool.OracleLteSource
import Benchmarks.UniswapV3.Pool.OracleObservationStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleZeroObservation : OracleObservation := ⟨⟨0⟩, 0, ⟨0⟩, false⟩

def oracleSearchFunction : FunctionDecl := contract.functions[41]!

theorem oracleSearchLookup :
    lookupCallable? contract "Oracle_binarySearch" = some oracleSearchFunction.toCallable := rfl

def oracleSearchLocals (time target index cardinality : UInt256) : Store :=
  ((((∅ : Store).insert "cardinality" (.int (Int.ofNat cardinality.toNat))).insert
    "index" (.int (Int.ofNat index.toNat))).insert "target"
    (.int (Int.ofNat target.toNat))).insert "time" (.int (Int.ofNat time.toNat))

def oracleSearchFrame (imms : Store) (time target index cardinality : UInt256) : Frame :=
  {contract := contract, locals := oracleSearchLocals time target index cardinality, immutables := imms}

theorem oracleSearchBind (time target index cardinality : UInt256) :
    bindParams? oracleSearchFunction.params [.int (Int.ofNat time.toNat),
      .int (Int.ofNat target.toNat), .int (Int.ofNat index.toNat),
      .int (Int.ofNat cardinality.toNat)] =
      some (oracleSearchLocals time target index cardinality) := rfl

def oracleSearchLeft (index cardinality : UInt256) : UInt256 :=
  UInt256.mod (UInt256.land (index + ⟨1⟩) (UInt256.ofNat 65535)) cardinality

def oracleSearchRight (index cardinality : UInt256) : UInt256 :=
  UInt256.sub (oracleSearchLeft index cardinality + cardinality) ⟨1⟩

def oracleSearchMiddle (left right : UInt256) : UInt256 := UInt256.div (left + right) ⟨2⟩

def oracleSearchBody : List Stmt :=
  match oracleSearchFunction.body[5]! with
  | .while _ body => body
  | _ => []

def oracleSearchZeroFrame (imms : Store) (time target index cardinality : UInt256) : Frame :=
  { (oracleSearchFrame imms time target index cardinality) with
    locals := ((oracleSearchLocals time target index cardinality).insert "beforeOrAt"
      oracleZeroObservation.value).insert "atOrAfter" oracleZeroObservation.value }

def oracleSearchReadyFrame (imms : Store) (time target index cardinality : UInt256) : Frame :=
  { (oracleSearchZeroFrame imms time target index cardinality) with
    locals := (((oracleSearchZeroFrame imms time target index cardinality).locals.insert "l"
      (.int (Int.ofNat (oracleSearchLeft index cardinality).toNat))).insert "r"
      (.int (Int.ofNat (oracleSearchRight index cardinality).toNat))).insert "i" (.int 0) }

theorem oracleObservationZeroPrefix (locals imms : Store) (evm : EVM.State) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (oracleSearchFunction.body.take 2)
      (.ok
        { contract := contract
          immutables := imms
          locals := (locals.insert "beforeOrAt" oracleZeroObservation.value).insert
            "atOrAfter" oracleZeroObservation.value } evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := oracleZeroObservation.value) ?_) ?_
  · simp [evalExpr?, evalStructFields?, oracleZeroObservation, OracleObservation.value,
      bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := oracleZeroObservation.value) ?_) ExecBlock.nil
  simp [evalExpr?, evalStructFields?, oracleZeroObservation, OracleObservation.value,
    bind, EvalResult.bind, pure]

theorem oracleSearchZeroPrefix (imms : Store) (evm : EVM.State)
    (time target index cardinality : UInt256) :
    ExecBlock config (oracleSearchFrame imms time target index cardinality) evm
      (oracleSearchFunction.body.take 2)
      (.ok (oracleSearchZeroFrame imms time target index cardinality) evm) :=
  oracleObservationZeroPrefix (oracleSearchLocals time target index cardinality) imms evm

theorem evalOracleSearchNextIndex {frame : Frame} {evm : EVM.State} (index : UInt256)
    (hi : frame.locals.get? "index" = some (.int (Int.ofNat index.toNat))) :
    evalExpr? config frame evm (.cast (.binary .add (.var "index") (.intLit 1))
      (.elem (.int (.uint ⟨16, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.land (index + ⟨1⟩) (UInt256.ofNat 65535)).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hi
  simp only [evalExpr?, he, bind, EvalResult.bind, pure, castValue?, evalBinaryOp?]
  rw [normalizeUIntInt_mask ⟨16, by decide⟩ _ (UInt256.ofNat 65535) (by decide),
    wordOfInt_add, wordOfInt_ofNat_toNat]
  rfl

theorem evalOracleSearchLeft {frame : Frame} {evm : EVM.State} (index cardinality : UInt256)
    (hi : frame.locals.get? "index" = some (.int (Int.ofNat index.toNat)))
    (hc : frame.locals.get? "cardinality" = some (.int (Int.ofNat cardinality.toNat)))
    (hn : cardinality.toNat ≠ 0) :
    evalExpr? config frame evm
      (.binary .mod (.cast (.binary .add (.var "index") (.intLit 1))
        (.elem (.int (.uint ⟨16, by decide⟩)))) (.var "cardinality")) =
      .ok (.int (Int.ofNat (oracleSearchLeft index cardinality).toNat)) :=
  evalExpr_word_mod (evalOracleSearchNextIndex index hi) (evalExpr_var_get hc) hn

theorem oracleSearchPrefix (imms : Store) (evm : EVM.State)
    (time target index cardinality : UInt256) (hn : cardinality.toNat ≠ 0) :
    ExecBlock config (oracleSearchFrame imms time target index cardinality) evm
      (oracleSearchFunction.body.take 5)
      (.ok (oracleSearchReadyFrame imms time target index cardinality) evm) := by
  let f0 := oracleSearchZeroFrame imms time target index cardinality
  let f1 := { f0 with
    locals := f0.locals.insert "l" (.int (Int.ofNat (oracleSearchLeft index cardinality).toNat)) }
  let f2 := { f1 with
    locals := f1.locals.insert "r" (.int (Int.ofNat (oracleSearchRight index cardinality).toNat)) }
  have hl := evalOracleSearchLeft (frame := f0) (evm := evm) index cardinality
    (by simp [f0, oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert])
    (by simp [f0, oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert]) hn
  have hr : evalExpr? config f1 evm
      (.cast (.binary .sub (.cast (.binary .add (.var "l") (.var "cardinality"))
        (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 1))
        (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (oracleSearchRight index cardinality).toNat)) := by
    apply evalExpr_word_sub (b := ⟨1⟩) ?_ (by simp only [evalExpr?, pure]; rfl)
    apply evalExpr_word_add
    · exact evalExpr_var_get (by simp [f1])
    · exact evalExpr_var_get (by
        simp [f1, f0, oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert])
  have htail : ExecBlock config f0 evm (oracleSearchFunction.body.drop 2 |>.take 3)
      (.ok (oracleSearchReadyFrame imms time target index cardinality) evm) := by
    refine ExecBlock.consNormal (solm' := f1) (evm' := evm) (ExecStmt.letDecl hl) ?_
    refine ExecBlock.consNormal (solm' := f2) (evm' := evm) (ExecStmt.letDecl hr) ?_
    exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil
  exact execBlock_append_ok (oracleSearchZeroPrefix imms evm time target index cardinality) htail

theorem oracleSearchRevertsZero (imms : Store) (evm : EVM.State)
    (time target index : UInt256) :
    ExecFuncBody config (oracleSearchFrame imms time target index ⟨0⟩) evm
      oracleSearchFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 oracleSearchFunction.body]
  apply execBlock_append_ok (oracleSearchZeroPrefix imms evm time target index ⟨0⟩)
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  have hi := evalOracleSearchNextIndex (frame := oracleSearchZeroFrame imms time target index ⟨0⟩)
    (evm := evm) index (by
      simp [oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert])
  have hc : evalExpr? config (oracleSearchZeroFrame imms time target index ⟨0⟩) evm
      (.var "cardinality") = .ok (.int 0) := evalExpr_var_get (by
    simp [oracleSearchZeroFrame, oracleSearchLocals, Std.HashMap.getElem_insert])
  exact evalExpr_int_mod_zero hi hc

theorem oracleSearchRemainder_lt (value cardinality : UInt256)
    (hn : cardinality.toNat ≠ 0) (hb : cardinality.toNat < 2 ^ 16) :
    (UInt256.mod value cardinality).toNat < 65535 := by
  rw [umod_toNat_of_ne_zero value cardinality hn]
  have hm := Nat.mod_lt value.toNat (Nat.pos_of_ne_zero hn)
  omega

theorem oracleSearchMiddle_lt (left right : UInt256) :
    (oracleSearchMiddle left right).toNat < 2 ^ 255 := by
  have hb := (left + right).val.isLt
  change (left + right).toNat < 2 ^ 256 at hb
  rw [oracleSearchMiddle, udiv_toNat]
  change (left + right).toNat / 2 < 2 ^ 255
  omega

end Benchmarks.UniswapV3.Pool
