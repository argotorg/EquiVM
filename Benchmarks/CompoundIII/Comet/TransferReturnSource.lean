import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def TransferReturnValid (out : ByteArray) : Prop :=
  out.size = 0 ∨ (out.size = 32 ∧ calldataWord out 0 ≠ ⟨0⟩)

instance (out : ByteArray) : Decidable (TransferReturnValid out) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

def transferReturnBlock : List Stmt :=
  [.require (.binary .eq (.arrayLength .localVar ⟨"data", []⟩) (.intLit 32)),
    .letDecl "result" (some abiUInt256) (.abiDecode abiUInt256 (.var "data")),
    .require (.binary .ne (.var "result") (.intLit 0))]

def transferReturnCallable : CallableDecl :=
  { params := [⟨"data", .bytes⟩], returnType := [], body :=
    [.ite (.binary .ne (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0))
      transferReturnBlock []] }

theorem transferReturnCallable_lookup :
    lookupCallable? contract "checkTransferReturn" = some transferReturnCallable := rfl

def transferReturnFrame (imms : Store) (out : ByteArray) : Frame :=
  { contract := contract, immutables := imms,
    locals := (∅ : Store).insert "data" (.bytes out) }

theorem transferReturn_length (imms : Store) (out : ByteArray) (evm : EVM.State) :
    evalExpr? config (transferReturnFrame imms out) evm
      (.arrayLength .localVar ⟨"data", []⟩) = .ok (.int (Int.ofNat out.size)) := by
  simp [evalExpr?, transferReturnFrame, readLocalPath?, pure, bind, EvalResult.bind]

theorem transferReturn_body (imms : Store) (out : ByteArray) (evm : EVM.State)
    (hh : out.size < 2^255) :
    if TransferReturnValid out then
      ∃ final, ExecFuncBody config (transferReturnFrame imms out) evm
        transferReturnCallable.body (.returned final evm none)
    else ExecFuncBody config (transferReturnFrame imms out) evm
      transferReturnCallable.body .reverted := by
  by_cases hz : out.size = 0
  · rw [if_pos (show TransferReturnValid out from Or.inl hz)]
    refine ⟨transferReturnFrame imms out, ExecFuncBody.execBlockOK ?_⟩
    apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
    simp [transferReturn_length, evalExpr?, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
      pure, bind, EvalResult.bind, hz]
  · by_cases h32 : out.size = 32
    · have hd : evalExpr? config (transferReturnFrame imms out) evm
          (.abiDecode abiUInt256 (.var "data")) =
          .ok (.int (Int.ofNat (calldataWord out 0).toNat)) := by
        simp only [evalExpr?, transferReturnFrame, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, EvalResult.ofOption, pure, bind, EvalResult.bind]
        change (match decodeReturnValue? abiUInt256 out with
          | some value => EvalResult.ok value | none => .revert) = _
        rw [decodeReturnUint_long (by omega) hh]
      by_cases hw : calldataWord out 0 = ⟨0⟩
      · rw [if_neg (by simp [TransferReturnValid, hz, hw])]
        apply ExecFuncBody.execBlockRevert
        apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
        · simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
            pure, bind, EvalResult.bind, hz]
        · apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
          · apply ExecBlock.consNormal (ExecStmt.letDecl hd)
            apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
            simp [evalExpr?, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
              pure, bind, EvalResult.bind, hw]
          · simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
              pure, bind, EvalResult.bind, h32]
      · rw [if_pos (show TransferReturnValid out from Or.inr ⟨h32, hw⟩)]
        refine ⟨{ transferReturnFrame imms out with locals :=
          ((transferReturnFrame imms out).locals.insert "result"
            (.int (Int.ofNat (calldataWord out 0).toNat))) }, ExecFuncBody.execBlockOK ?_⟩
        apply ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
        · simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
            pure, bind, EvalResult.bind, hz]
        · apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
          · apply ExecBlock.consNormal (ExecStmt.letDecl hd)
            apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
            simp [evalExpr?, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
              pure, bind, EvalResult.bind]
            exact fun h ↦ hw (uint256_toNat_eq_zero h)
          · simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
              pure, bind, EvalResult.bind, h32]
    · rw [if_neg (by simp [TransferReturnValid, hz, h32])]
      apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
      · simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
          pure, bind, EvalResult.bind, hz]
      · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        simp [evalExpr?, transferReturnFrame, evalBinaryOp?, readLocalPath?, EvalResult.ofOption,
          pure, bind, EvalResult.bind, h32]
        exact_mod_cast h32

theorem transferReturn_call (frame : Frame) (evm : EVM.State) (expr : Expr) (ret : Ident)
    (out : ByteArray) (hf : frame.contract = contract)
    (he : evalExpr? config frame evm expr = .ok (.bytes out)) (hh : out.size < 2^255) :
    ExecStmt config frame evm (.internalCall "checkTransferReturn" [expr] ret)
      (if TransferReturnValid out then
        .ok { frame with locals := frame.locals.insert ret .unit } evm else .reverted) := by
  have hb := transferReturn_body frame.immutables out evm hh
  by_cases hv : TransferReturnValid out
  · rw [if_pos hv] at hb ⊢
    obtain ⟨final, hb⟩ := hb
    exact ExecStmt.internalCallReturn (callee := transferReturnCallable)
      (argVals := [.bytes out]) (locals := (∅ : Store).insert "data" (.bytes out)) (value := none)
      (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
      (by rw [hf]; exact transferReturnCallable_lookup) rfl (by simpa only [hf] using hb)
  · rw [if_neg hv] at hb ⊢
    exact ExecStmt.internalCallRevert (callee := transferReturnCallable)
      (argVals := [.bytes out]) (locals := (∅ : Store).insert "data" (.bytes out))
      (by simp only [evalExprs?, he, pure, bind, EvalResult.bind])
      (by rw [hf]; exact transferReturnCallable_lookup) rfl (by simpa only [hf] using hb)

end Benchmarks.CompoundIII.Comet
