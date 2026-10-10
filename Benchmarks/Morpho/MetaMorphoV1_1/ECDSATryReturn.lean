import Benchmarks.Morpho.MetaMorphoV1_1.ECDSATrySource

/-! Decode a recovery result and return the signer with its ECDSA error code. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

theorem ecdsaZeroBytes : wordBytes32Value (⟨0⟩ : UInt256) =
    .fixedBytes abiBytes32Width (List.replicate 32 0) := by native_decide

def ecdsaRecoveryError (signer : AccountAddress) : UInt256 :=
  if signer = AccountAddress.ofNat 0 then ⟨1⟩ else ⟨0⟩

theorem ecdsaSignerTail {evm : State} {frame : Frame} {signer : AccountAddress}
    (hget : frame.locals.get? "signer" = some (.address signer)) :
    ExecBlock config frame evm (ecdsaTryFunction.body.drop 7)
      (.returned frame evm (some [.address signer, uint256Value (ecdsaRecoveryError signer),
        wordBytes32Value ⟨0⟩])) := by
  have hs : evalExpr? config frame evm (.var "signer") = .ok (.address signer) := by
    simp only [evalExpr?, hget, EvalResult.ofOption]
  have hz : evalExpr? config frame evm (.cast (.intLit 0) (.elem .address)) =
      .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption]
    rfl
  have hc := evalExpr_addressEq hs hz
  by_cases hzero : signer = AccountAddress.ofNat 0
  · simp only [hzero, decide_true] at hc
    apply ExecBlock.consReturn (ExecStmt.iteTrue hc ?_)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, hz, evalExpr?, bind, EvalResult.bind, pure,
      ecdsaRecoveryError, hzero, if_true, ecdsaZeroBytes]
    rfl
  · simp only [hzero, decide_false] at hc
    apply ExecBlock.consNormal (ExecStmt.iteFalse hc ExecBlock.nil)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, hs, evalExpr?, bind, EvalResult.bind, pure,
      ecdsaRecoveryError, if_neg hzero, ecdsaZeroBytes]
    rfl

theorem ecdsaOutputCondition {evm : State} {frame : Frame} {out : ByteArray}
    (hget : frame.locals.get? "output" = some (.bytes out)) :
    evalExpr? config frame evm
      (.binary .ne (.arrayLength .localVar ⟨"output", []⟩) (.intLit 0)) =
      .ok (.bool (decide (out.size ≠ 0))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure]
  simp [evalBinaryOp?, BEq.beq]

theorem ecdsaDecodeSigner {evm : State} {frame : Frame} {out : ByteArray}
    (hget : frame.locals.get? "output" = some (.bytes out)) (hout : EcrecoverOutput out) :
    ∃ frame', ExecBlock config frame evm ((ecdsaTryFunction.body.drop 5).take 2)
      (.ok frame' evm) ∧ frame'.locals.get? "signer" = some (.address (ecrecoverSigner out)) := by
  let zeroFrame : Frame :=
    { frame with locals := frame.locals.insert "signer" (.address (AccountAddress.ofNat 0)) }
  have hlet : ExecStmt config frame evm
      (.letDecl "signer" (some abiAddress) (.cast (.intLit 0) (.elem .address)))
      (.ok zeroFrame evm) := by
    apply ExecStmt.letDecl
    simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?, EvalResult.ofOption]
    rfl
  have ho : zeroFrame.locals.get? "output" = some (.bytes out) := by
    change (frame.locals.insert "signer" _).get? "output" = _
    rw [store_get_ne _ _ (by decide), hget]
  have hc := ecdsaOutputCondition (evm := evm) ho
  rcases hout with hempty | ⟨hsize, hcanon⟩
  · subst out
    refine ⟨zeroFrame, ExecBlock.consNormal hlet
      (ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil), ?_⟩
    · simpa only [show ByteArray.empty.size = 0 from rfl, ne_eq, not_true_eq_false,
        decide_false] using hc
    · rw [ecrecoverSigner_empty]
      exact store_get_self _ _ _
  · let decoded : Frame :=
      { zeroFrame with locals := zeroFrame.locals.insert "signer" (.address (ecrecoverSigner out)) }
    refine ⟨decoded, ExecBlock.consNormal hlet
      (ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil), store_get_self _ _ _⟩
    · simpa only [hsize, ne_eq, show ¬ (32 : Nat) = 0 by decide, not_false_eq_true,
        decide_true] using hc
    · apply ExecBlock.consNormal (ExecStmt.assign (value := .address (ecrecoverSigner out)) ?_ ?_)
        ExecBlock.nil
      · simp only [evalExpr?, ho, EvalResult.ofOption, bind, EvalResult.bind]
        change (match decodeReturnValue? abiAddress out with
          | some value => EvalResult.ok value | none => EvalResult.revert) = _
        rw [ecrecoverAddressDecode hsize hcanon]
      · simp only [assignStorageRef?, zeroFrame, store_get_self, updateLocalPath?,
          bind, EvalResult.bind, pure]
        rfl

theorem ecdsaTryReturns {evm evm' : State} (imms : Store) (hash sigV sigR sigS : UInt256)
    (out : ByteArray) (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (true, evm', out) false) :
    ∃ frame', ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaTryFunction.body
      (.returned frame' evm' (some [.address (ecrecoverSigner out),
        uint256Value (ecdsaRecoveryError (ecrecoverSigner out)), wordBytes32Value ⟨0⟩])) := by
  obtain ⟨frame', hdecode, hsigner⟩ := ecdsaDecodeSigner
    (frame := ecdsaCallFrame imms hash sigV sigR sigS true out) (evm := evm')
    (store_get_self _ _ _) (callEcrecoverOutput hcall)
  refine ⟨frame', ExecFuncBody.execBlockRet ?_⟩
  apply ecdsaTryPrefix imms hash sigV sigR sigS true out hlow hcall
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_)
  · exact execBlock_append_ok hdecode (ecdsaSignerTail hsigner)
  · simp [evalExpr?, ecdsaCallFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem ecdsaTryHighCall {evm : State} {locals imms : Store}
    {hash sigV sigR sigS : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS])
    (hhigh : ecdsaHalfOrder < sigS.toNat) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA_tryRecover" args ret)
      (.ok ⟨contract, locals.insert ret (.tuple [.address (AccountAddress.ofNat 0), .int 3,
        wordBytes32Value sigS]), imms⟩ evm) :=
  internalCallFunctionReturn (callee := ecdsaTryFunction) hargs rfl rfl
    (ecdsaTryHighBody evm imms hash sigV sigR sigS hhigh)

theorem ecdsaTryCall {evm evm' : State} {locals imms : Store}
    {hash sigV sigR sigS : UInt256} {args : List Expr} {ret : Ident} {out : ByteArray}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS])
    (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (true, evm', out) false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA_tryRecover" args ret)
      (.ok ⟨contract, locals.insert ret (.tuple [.address (ecrecoverSigner out),
        uint256Value (ecdsaRecoveryError (ecrecoverSigner out)), wordBytes32Value ⟨0⟩]), imms⟩
        evm') := by
  obtain ⟨frame', hbody⟩ := ecdsaTryReturns imms hash sigV sigR sigS out hlow hcall
  exact internalCallFunctionReturn (callee := ecdsaTryFunction) hargs rfl rfl hbody

theorem ecdsaTryCallReverts {evm evm' : State} {locals imms : Store}
    {hash sigV sigR sigS : UInt256} {args : List Expr} {ret : Ident} {out : ByteArray}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS])
    (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (false, evm', out) false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA_tryRecover" args ret)
      .reverted :=
  ExecStmt.internalCallRevert (callee := ecdsaTryFunction.toCallable) hargs rfl rfl
    (ecdsaTryCallFailed imms hash sigV sigR sigS out hlow hcall)

end Benchmarks.Morpho.MetaMorphoV1_1
