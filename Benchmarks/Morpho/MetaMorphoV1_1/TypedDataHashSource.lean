import Benchmarks.Morpho.MetaMorphoV1_1.DomainSource

/-! The EIP-712 envelope and the source helper that obtains its domain separator. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

def typedDataPreimage (domain structHash : UInt256) : ByteArray :=
  ([25, 1] : List UInt8).toByteArray ++ domain.toByteArray ++ structHash.toByteArray

def typedDataHash (domain structHash : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (typedDataPreimage domain structHash))

def toTypedDataHashFunction : FunctionDecl := contract.functions[69]!

def toTypedDataHashFrame (imms : Store) (domain structHash : UInt256) : Frame :=
  ⟨contract, ((∅ : Store).insert "structHash" (wordBytes32Value structHash)).insert
    "domainSeparator" (wordBytes32Value domain), imms⟩

theorem toTypedDataHashBody (evm : State) (imms : Store) (domain structHash : UInt256) :
    ExecFuncBody config (toTypedDataHashFrame imms domain structHash) evm
      toTypedDataHashFunction.body
      (.returned (toTypedDataHashFrame imms domain structHash) evm
        (some [wordBytes32Value (typedDataHash domain structHash)])) := by
  have hprefix : evalExpr? config (toTypedDataHashFrame imms domain structHash) evm
      (.fixedBytesLit ⟨1, by decide⟩ [25, 1]) =
      .ok (.fixedBytes ⟨1, by decide⟩ [25, 1]) := by simp only [evalExpr?, pure]
  have hdomain : evalExpr? config (toTypedDataHashFrame imms domain structHash) evm
      (.var "domainSeparator") = .ok (wordBytes32Value domain) := by
    simp only [evalExpr?, toTypedDataHashFrame, store_get_self, EvalResult.ofOption]
  have hstruct : evalExpr? config (toTypedDataHashFrame imms domain structHash) evm
      (.var "structHash") = .ok (wordBytes32Value structHash) := by
    simp only [evalExpr?, toTypedDataHashFrame,
      store_get_ne _ _ (by decide : ("domainSeparator" == "structHash") = false),
      store_get_self, EvalResult.ofOption]
  have hpack := evalExpr_packed (evalPackedArgs_cons hprefix
    (show encodePackedValue? (.elem (.bytes ⟨1, by decide⟩))
      (.fixedBytes ⟨1, by decide⟩ [25, 1]) = some [25, 1] by decide +kernel)
    (evalPackedArgs_cons hdomain (encodePacked_bytes32 domain)
      (evalPackedArgs_cons (args := []) (tail := []) hstruct (encodePacked_bytes32 structHash)
        (by simp only [evalPackedArgs?, pure]))))
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_keccakWord
  simpa only [typedDataHash, typedDataPreimage, List.append_nil, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc] using hpack

theorem toTypedDataHashCall {evm : State} {locals imms : Store}
    {domain structHash : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [wordBytes32Value domain, wordBytes32Value structHash]) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "MessageHashUtils_toTypedDataHash" args ret)
      (.ok ⟨contract, locals.insert ret (wordBytes32Value (typedDataHash domain structHash)), imms⟩
        evm) :=
  internalCallFunctionReturn (callee := toTypedDataHashFunction) hargs rfl rfl
    (toTypedDataHashBody evm imms domain structHash)

def hashTypedDataFunction : FunctionDecl := contract.functions[34]!

def hashTypedDataFrame (v : MetaMorphoV1_1Immutables) (structHash : UInt256) : Frame :=
  domainFrame v ((∅ : Store).insert "structHash" (wordBytes32Value structHash))

theorem hashTypedDataBody (evm : State) (v : MetaMorphoV1_1Immutables) (structHash : UInt256) :
    ∃ frame', ExecFuncBody config (hashTypedDataFrame v structHash) evm hashTypedDataFunction.body
      (.returned frame' evm (some [wordBytes32Value
        (typedDataHash (domainSeparatorWord v evm.executionEnv) structHash)])) := by
  let locals := (hashTypedDataFrame v structHash).locals
  let domain := domainSeparatorWord v evm.executionEnv
  let next := locals.insert "__c0" (wordBytes32Value domain)
  refine ⟨domainFrame v (next.insert "__c1" (wordBytes32Value (typedDataHash domain structHash))),
    ExecFuncBody.execBlockRet ?_⟩
  refine ExecBlock.consNormal (domainSeparatorCall evm v locals "__c0") ?_
  refine ExecBlock.consNormal (toTypedDataHashCall
    (domain := domain) (structHash := structHash) ?_) ?_
  · simp only [evalExprs?, evalExpr?, locals, hashTypedDataFrame, domainFrame, store_get_self,
      EvalResult.ofOption, store_get_ne _ _ (by decide : ("__c0" == "structHash") = false),
      bind, EvalResult.bind, pure]
    rfl
  · exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
      simp only [evalExpr?, store_get_self, EvalResult.ofOption]
      rfl)))

theorem hashTypedDataCall {evm : State} (v : MetaMorphoV1_1Immutables) {locals : Store}
    {structHash : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config (domainFrame v locals) evm args =
      .ok [wordBytes32Value structHash]) :
    ExecStmt config (domainFrame v locals) evm (.internalCall "_hashTypedDataV4" args ret)
      (.ok (domainFrame v (locals.insert ret (wordBytes32Value
        (typedDataHash (domainSeparatorWord v evm.executionEnv) structHash)))) evm) := by
  obtain ⟨frame', hbody⟩ := hashTypedDataBody evm v structHash
  exact internalCallFunctionReturn (callee := hashTypedDataFunction) hargs rfl rfl hbody

end Benchmarks.Morpho.MetaMorphoV1_1
