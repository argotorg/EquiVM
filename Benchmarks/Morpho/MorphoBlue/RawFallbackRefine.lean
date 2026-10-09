import Benchmarks.Morpho.MorphoBlue.RawReturnBlockRefines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

variable {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
  {immutables callargs : Store} {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
  {g : UInt256} {code : ByteArray}

-- LIBRARY CANDIDATE: reverting raw fallback execution without ABI selector dispatch.
theorem reEquivRawFallbackRevert (hcode : I.code = code)
    (h : RDrev code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hd : selectorDispatchMsg contract I.calldata = none)
    (hr : receiveDispatchMsg contract I.calldata = none) (hf : contract.fallback = some t)
    (ha : fallbackCallargs I.calldata t.params = some callargs)
    (hc : fallbackReturnConvention t = some .rawBytes)
    (hb : ExecTransitionBody cfg contract (initState σ σ₀ (.ofUInt256 g) A I)
      callargs t.body .reverted immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  apply RDrev.reEquivElim hcode h
  intro g' out hxi
  refine .execution rfl (.fallback hd hr hf ha hc rfl hb) ?_
  rw [hxi]
  exact .revert rfl rfl

-- LIBRARY CANDIDATE: a raw-return block proof completes a fallback refinement.
theorem RawReturnBlockRefines.fallback (hcode : I.code = code)
    (hd : selectorDispatchMsg contract I.calldata = none)
    (hr : receiveDispatchMsg contract I.calldata = none) (hf : contract.fallback = some t)
    (ha : fallbackCallargs I.calldata t.params = some callargs)
    (hc : fallbackReturnConvention t = some .rawBytes)
    (h : RawReturnBlockRefines cfg code I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I)
      { contract := contract, locals := callargs, immutables := immutables }
      (initState σ σ₀ (.ofUInt256 g) A I) t.body) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  cases h with
  | reverted he hx =>
    exact reEquivRawFallbackRevert hcode hx hd hr hf ha hc (ExecFuncBody.execBlockRevert he)
  | static he hx =>
    apply RDstatic.reEquivElim hcode hx
    intro hxi
    refine .execution rfl (.fallback hd hr hf ha hc rfl (ExecFuncBody.execBlockStatic he)) ?_
    rw [hxi]
    exact .staticHalt rfl rfl
  | ok he hs hx =>
    rcases hx with hoog | ⟨s, hX, hacc⟩
    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
    · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
      rw [hacc] at hxi
      refine .execution rfl (.fallback hd hr hf ha hc rfl (ExecFuncBody.execBlockRet he)) ?_
      rw [hxi]
      exact .success rfl rfl hs.accounts (.rawBytes rfl)

end Benchmarks.Morpho.MorphoBlue
