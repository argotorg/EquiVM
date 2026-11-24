import Tests.Pipeline.VyperWrapper.Helpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `token()`

Dispatcher bucket 2, arm entry pc 1651: the `callvalue` guard, then the immutable section copied
from the code (pc 1656) and returned.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem tokenBody_eq : tokenTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.immutable "TOKEN"]] := by rfl

/-- `token()`: the theorem `Correct.lean` routes selector 7 to. -/
theorem wrapperTokenBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 7) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := token_of_fit hfit
  obtain ⟨_, _, rd⟩ := wrapperReachTokenBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some tokenTransition :=
    wrapperDispatch_token (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (tokenTransition.params.map Param.name)
      (transitionSignature tokenTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, tokenTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := wrapperBlocks.wrapper_block_1651_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := wrapperBlocks.wrapper_block_1656 (immWords := wordsOf imms) (by simp) rd1
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ tokenTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [.address a]))
        (restrictImmutables contract imms) := by
      rw [tokenBody_eq]
      exact ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns
          (evalImmutable_TOKEN hget ∅ _))
    exact rd2.reEquivExecution hcode' hd hdec hbody
      (returnEquiv_of_encode (by rw [suffixWords_TOKEN, wordsOf_TOKEN hget]; exact addressReturnEncoding a))
  · have rd1 := wrapperBlocks.wrapper_block_1651_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [tokenBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperWrapper
