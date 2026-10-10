import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Reasoning.ExternalCall

/-! Source behavior of Address.verifyCallResultFromTarget and its revert helper. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option maxRecDepth 2000

def addressVerifyFunction : FunctionDecl := contract.functions[67]!

def addressRevertFunction : FunctionDecl := contract.functions[88]!

def addressVerifyFrame (imms : Store) (target : AccountAddress) (ok : Bool)
    (out : ByteArray) : Frame :=
  ⟨contract, (((∅ : Store).insert "returndata" (.bytes out)).insert "success" (.bool ok)).insert
    "target" (.address target), imms⟩

def addressReturnValid (evm : State) (target : AccountAddress) (out : ByteArray) : Prop :=
  out.size ≠ 0 ∨ extCodeSizeWord evm.accountMap (UInt256.ofNat target.toNat) ≠ ⟨0⟩

instance (evm : State) (target : AccountAddress) (out : ByteArray) :
    Decidable (addressReturnValid evm target out) := inferInstanceAs (Decidable (_ ∨ _))

theorem addressVerifySuccessSource (evm : State) (imms : Store) (target : AccountAddress)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (addressVerifyFrame imms target ok out) evm
      (.unary .not (.var "success")) = .ok (.bool (!ok)) := by
  simp only [evalExpr?, addressVerifyFrame,
    store_get_ne _ _ (show ("target" == "success") = false by decide), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]

theorem addressVerifyGuardSource (evm : State) (imms : Store) (target : AccountAddress)
    (ok : Bool) (out : ByteArray) :
    evalExpr? config (addressVerifyFrame imms target ok out) evm
      (.unary .not (.binary .and
        (.binary .eq (.arrayLength .localVar ⟨"returndata", []⟩) (.intLit 0))
        (.binary .eq (.extCodeSize (.var "target")) (.intLit 0)))) =
      .ok (.bool (decide (addressReturnValid evm target out))) := by
  have ht : evalExpr? config (addressVerifyFrame imms target ok out) evm (.var "target") =
      .ok (.address (AccountAddress.ofUInt256 (UInt256.ofNat target.toNat))) := by
    have ha : AccountAddress.ofUInt256 (UInt256.ofNat target.toNat) = target := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      exact accountAddress_of_word_val target
    rw [ha]
    simp [evalExpr?, addressVerifyFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  have hc := extCodeSource (cfg := config) rfl ht
  have hl : evalExpr? config (addressVerifyFrame imms target ok out) evm
      (.arrayLength .localVar ⟨"returndata", []⟩) = .ok (.int (Int.ofNat out.size)) := by
    simp [evalExpr?, addressVerifyFrame, Std.HashMap.getElem_insert, readLocalPath?,
      bind, EvalResult.bind, pure]
  have hz : evalExpr? config (addressVerifyFrame imms target ok out) evm (.intLit 0) =
      .ok (.int (Int.ofNat 0)) := by simp only [evalExpr?, pure]; rfl
  have heq {a : Expr} {n : Nat}
      (ha : evalExpr? config (addressVerifyFrame imms target ok out) evm a =
        .ok (.int (Int.ofNat n))) :
      evalExpr? config (addressVerifyFrame imms target ok out) evm
        (.binary .eq a (.intLit 0)) = .ok (.bool (decide (n = 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [ha, hz, bind, EvalResult.bind, evalBinaryOp_eq_int_ok]
    simp [BEq.beq]
  have hand := boolAndSource (heq hl) (heq hc)
  simp only [evalExpr?, hand, bind, EvalResult.bind, evalUnaryOp?]
  have hziff : (extCodeSizeWord evm.accountMap (UInt256.ofNat target.toNat)).toNat = 0 ↔
      extCodeSizeWord evm.accountMap (UInt256.ofNat target.toNat) = ⟨0⟩ :=
    ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simp only [hziff]
  simp [addressReturnValid, EvalResult.ofOption]
  rfl

theorem addressVerifyBodyReturns (evm : State) (imms : Store) (target : AccountAddress)
    (out : ByteArray) (hvalid : addressReturnValid evm target out) :
    ExecFuncBody config (addressVerifyFrame imms target true out) evm
      addressVerifyFunction.body
      (.returned (addressVerifyFrame imms target true out) evm (some [.bytes out])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.iteFalse (addressVerifySuccessSource ..) ?_)
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [hvalid, decide_true] using addressVerifyGuardSource evm imms target true out))
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp [evalExpr?, addressVerifyFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem addressVerifyBodyRevertsCode (evm : State) (imms : Store) (target : AccountAddress)
    (out : ByteArray) (hbad : ¬ addressReturnValid evm target out) :
    ExecFuncBody config (addressVerifyFrame imms target true out) evm
      addressVerifyFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.iteFalse (addressVerifySuccessSource ..) ?_)
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    simpa only [hbad, decide_false] using addressVerifyGuardSource evm imms target true out))

theorem addressVerifyBodyRevertsCall (evm : State) (imms : Store) (target : AccountAddress)
    (out : ByteArray) :
    ExecFuncBody config (addressVerifyFrame imms target false out) evm
      addressVerifyFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert (ExecStmt.iteTrue (addressVerifySuccessSource ..) ?_)
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (callee := addressRevertFunction) (argVals := [.bytes out])
    (by simp [evalExprs?, evalExpr?, addressVerifyFrame, Std.HashMap.getElem_insert,
          EvalResult.ofOption, bind, EvalResult.bind, pure]) rfl rfl
  exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (by
    simp only [evalExpr?, pure])))

theorem addressVerifyCallReturns (evm : State) (locals imms : Store) (target : AccountAddress)
    (out : ByteArray) (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bool true, .bytes out])
    (hvalid : addressReturnValid evm target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "Address_verifyCallResultFromTarget" args retVar)
      (.ok ⟨contract, locals.insert retVar (.bytes out), imms⟩ evm) :=
  internalCallFunctionReturn (callee := addressVerifyFunction) hargs rfl rfl
    (addressVerifyBodyReturns evm imms target out hvalid)

theorem addressVerifyCallReverts (evm : State) (locals imms : Store) (target : AccountAddress)
    (ok : Bool) (out : ByteArray) (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bool ok, .bytes out])
    (hbad : ok = false ∨ ¬ addressReturnValid evm target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "Address_verifyCallResultFromTarget" args retVar) .reverted := by
  apply internalCallFunctionRevert (callee := addressVerifyFunction) hargs rfl rfl
  cases ok with
  | false => exact addressVerifyBodyRevertsCall evm imms target out
  | true =>
      exact addressVerifyBodyRevertsCode evm imms target out (hbad.resolve_left (by decide))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
