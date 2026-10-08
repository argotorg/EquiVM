import Benchmarks.CompoundIII.Comet.DispatchRules

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: the empty ABI encoding of a void function's fallthrough.
theorem voidReturnEquiv : returnEquiv ByteArray.empty none [] := by
  apply returnEquiv.fallthrough rfl rfl
  simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?]
  rfl

-- GENERALIZES Reasoning.Dispatch.RDret.reEquivExecutionGen to selector dispatch with fallback.
theorem selectorStateReturn_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code out : ByteArray} {args frame values}
    {σ' : AccountMap} {evm' : EVM.State}
    (hcode : I.code = code)
    (h : RDret code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ' out)
    (hd : selectorDispatchMsg C I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      args t.body (.returned frame evm' values) imms)
    (haccounts : σ' = evm'.accountMap) (henc : returnEquiv out values t.returnType) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    exact .execution hxi (.intro hd rfl hdec rfl hbody)
      (.success rfl rfl (hacc.trans haccounts) (.abi henc))

-- GENERALIZES Reasoning.Reach.RDstatic.reEquivStaticHalt to selector dispatch with fallback.
theorem selectorStatic_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args}
    (hcode : I.code = code)
    (h : RDstatic code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hd : selectorDispatchMsg C I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      args t.body .staticViolation imms) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  exact h.reEquivElim hcode fun hxi ↦
    .execution hxi (.intro hd rfl hdec rfl hbody) (.staticHalt rfl rfl)

-- GENERALIZES Reasoning.Dispatch.RDret.reEquivExecution — take successful
-- selector dispatch directly, so named calls work in contracts with a fallback.
theorem selectorReturn_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code out : ByteArray} {args frame values}
    (hcode : I.code = code)
    (h : RDret code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out)
    (hd : selectorDispatchMsg C I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      args t.body (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) values) imms)
    (henc : returnEquiv out values t.returnType) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  exact selectorStateReturn_refines hcode h hd hdec hbody rfl henc

-- GENERALIZES Reasoning.Dispatch.RDrev.reEquivExecutionRevert — the same
-- selector-dispatch interface for reverts in contracts with a fallback.
theorem selectorRevert_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray} {args}
    (hcode : I.code = code)
    (h : RDrev code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hd : selectorDispatchMsg C I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      args t.body .reverted imms) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  exact h.reEquivElim hcode fun _ _ hxi ↦
    .execution hxi (.intro hd rfl hdec rfl hbody) (.revert rfl rfl)

-- GENERALIZES Reasoning.Reach.RDrev.reEquivDecodingFailed to contracts with fallback.
theorem selectorDecodeFailure_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hd : selectorDispatchMsg C I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none) :
    runtimeRefinementFor cfg C σ σ₀ g A I imms := by
  exact h.reEquivElim hcode fun _ _ hxi ↦ .decodingFailed hd rfl hdec hxi

end Benchmarks.CompoundIII.Comet
