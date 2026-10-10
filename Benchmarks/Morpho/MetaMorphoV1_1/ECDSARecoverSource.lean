import Benchmarks.Morpho.MetaMorphoV1_1.ECDSAErrorSource

/-! Compose recovery and error handling at the source internal-call boundary. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def ecdsaRecoverFunction : FunctionDecl := contract.functions[35]!

def ecdsaFieldsFrame (locals imms : Store) (signer : AccountAddress)
    (error errorArg : UInt256) : Frame :=
  ⟨contract, ((locals.insert "recovered" (.address signer)).insert
    "error" (uint256Value error)).insert "errorArg" (wordBytes32Value errorArg), imms⟩

theorem ecdsaRecoverFields {evm : State} {locals imms : Store} {signer : AccountAddress}
    {error errorArg : UInt256} {result : ExecResult}
    (hget : locals.get? "__c0" =
      some (.tuple [.address signer, uint256Value error, wordBytes32Value errorArg]))
    (htail : ExecBlock config (ecdsaFieldsFrame locals imms signer error errorArg) evm
      (ecdsaRecoverFunction.body.drop 4) result) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (ecdsaRecoverFunction.body.drop 1) result := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address signer) ?_) ?_
  · simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value error) ?_) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("recovered" == "__c0") = false),
      hget, EvalResult.ofOption, bind, EvalResult.bind]; rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value errorArg) ?_) htail
  simp only [evalExpr?, store_get_ne _ _ (by decide : ("error" == "__c0") = false),
    store_get_ne _ _ (by decide : ("recovered" == "__c0") = false),
    hget, EvalResult.ofOption, bind, EvalResult.bind]; rfl

theorem ecdsaFieldsArgs (evm : State) (locals imms : Store) (signer : AccountAddress)
    (error errorArg : UInt256) :
    evalExprs? config (ecdsaFieldsFrame locals imms signer error errorArg) evm
      [.var "error", .var "errorArg"] = .ok [uint256Value error, wordBytes32Value errorArg] := by
  simp only [evalExprs?, evalExpr?, ecdsaFieldsFrame,
    store_get_ne _ _ (by decide : ("errorArg" == "error") = false), store_get_self,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem ecdsaRecoverTailReturns (evm : State) (locals imms : Store) (signer : AccountAddress)
    (errorArg : UInt256) :
    ∃ frame', ExecBlock config (ecdsaFieldsFrame locals imms signer ⟨0⟩ errorArg) evm
      (ecdsaRecoverFunction.body.drop 4) (.returned frame' evm (some [.address signer])) := by
  refine ⟨⟨contract, (ecdsaFieldsFrame locals imms signer ⟨0⟩ errorArg).locals.insert
    "__c1" .unit, imms⟩, ?_⟩
  apply ExecBlock.consNormal (ecdsaThrowCall (ecdsaFieldsArgs evm locals imms signer ⟨0⟩ errorArg))
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp [evalExpr?, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem ecdsaRecoverTailReverts (evm : State) (locals imms : Store) (signer : AccountAddress)
    (error errorArg : UInt256) (hne : error ≠ ⟨0⟩) :
    ExecBlock config (ecdsaFieldsFrame locals imms signer error errorArg) evm
      (ecdsaRecoverFunction.body.drop 4) .reverted :=
  ExecBlock.consRevert
    (ecdsaThrowCallReverts (ecdsaFieldsArgs evm locals imms signer error errorArg) hne)

theorem ecdsaFrameArgs (evm : State) (imms : Store) (hash sigV sigR sigS : UInt256) :
    evalExprs? config (ecdsaFrame imms hash sigV sigR sigS) evm
      [.var "hash", .var "v", .var "r", .var "s"] =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS] :=
        by
  simp [evalExprs?, evalExpr?, ecdsaFrame, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem ecdsaRecoverHighBody (evm : State) (imms : Store) (hash sigV sigR sigS : UInt256)
    (hhigh : ecdsaHalfOrder < sigS.toNat) :
    ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaRecoverFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ecdsaTryHighCall (ecdsaFrameArgs evm imms hash sigV sigR sigS) hhigh)
  apply ecdsaRecoverFields (error := ⟨3⟩) (errorArg := sigS) (store_get_self _ _ _)
  exact ecdsaRecoverTailReverts evm _ imms (AccountAddress.ofNat 0) ⟨3⟩ sigS (by decide)

theorem ecdsaRecoverCallFailed {evm evm' : State} (imms : Store) (hash sigV sigR sigS : UInt256)
    (out : ByteArray) (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (false, evm', out) false) :
    ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaRecoverFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact ExecBlock.consRevert
    (ecdsaTryCallReverts (ecdsaFrameArgs evm imms hash sigV sigR sigS) hlow hcall)

theorem ecdsaRecoverInvalidBody {evm evm' : State} (imms : Store)
    (hash sigV sigR sigS : UInt256) (out : ByteArray) (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (true, evm', out) false)
    (hzero : ecrecoverSigner out = AccountAddress.ofNat 0) :
    ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaRecoverFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ecdsaTryCall (ecdsaFrameArgs evm imms hash sigV sigR sigS) hlow hcall)
  apply ecdsaRecoverFields (store_get_self _ _ _)
  apply ecdsaRecoverTailReverts
  rw [ecdsaRecoveryError, if_pos hzero]
  decide

theorem ecdsaRecoverReturns {evm evm' : State} (imms : Store) (hash sigV sigR sigS : UInt256)
    (out : ByteArray) (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (true, evm', out) false)
    (hne : ecrecoverSigner out ≠ AccountAddress.ofNat 0) :
    ∃ frame', ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm ecdsaRecoverFunction.body
      (.returned frame' evm' (some [.address (ecrecoverSigner out)])) := by
  let locals := (ecdsaFrame imms hash sigV sigR sigS).locals.insert "__c0"
    (.tuple [.address (ecrecoverSigner out), uint256Value ⟨0⟩, wordBytes32Value ⟨0⟩])
  obtain ⟨frame', htail⟩ := ecdsaRecoverTailReturns evm' locals imms (ecrecoverSigner out) ⟨0⟩
  refine ⟨frame', ExecFuncBody.execBlockRet ?_⟩
  have htry := ecdsaTryCall (ecdsaFrameArgs evm imms hash sigV sigR sigS) hlow hcall (ret := "__c0")
  rw [ecdsaRecoveryError, if_neg hne] at htry
  apply ExecBlock.consNormal htry
  exact ecdsaRecoverFields (store_get_self _ _ _) htail

theorem ecdsaRecoverCall {evm evm' : State} {locals imms : Store}
    {hash sigV sigR sigS : UInt256} {args : List Expr} {ret : Ident} {out : ByteArray}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS])
    (hlow : ¬ ecdsaHalfOrder < sigS.toNat)
    (hcall : callViaEVM evm (AccountAddress.ofNat 1) 0
      (ecrecoverInput hash sigV sigR sigS) (true, evm', out) false)
    (hne : ecrecoverSigner out ≠ AccountAddress.ofNat 0) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA_recover" args ret)
      (.ok ⟨contract, locals.insert ret (.address (ecrecoverSigner out)), imms⟩ evm') := by
  obtain ⟨frame', hbody⟩ := ecdsaRecoverReturns imms hash sigV sigR sigS out hlow hcall hne
  exact internalCallFunctionReturn (callee := ecdsaRecoverFunction) hargs rfl rfl hbody

theorem ecdsaRecoverCallReverts {evm : State} {locals imms : Store}
    {hash sigV sigR sigS : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value hash, uint256Value sigV, wordBytes32Value sigR, wordBytes32Value sigS])
    (hbody : ExecFuncBody config (ecdsaFrame imms hash sigV sigR sigS) evm
      ecdsaRecoverFunction.body .reverted) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA_recover" args ret)
      .reverted :=
  ExecStmt.internalCallRevert (callee := ecdsaRecoverFunction.toCallable) hargs rfl rfl hbody

end Benchmarks.Morpho.MetaMorphoV1_1
