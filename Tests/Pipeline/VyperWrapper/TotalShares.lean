import Tests.Pipeline.VyperWrapper.Helpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `totalShares()`

Dispatcher bucket 1, arm entry pc 1740: the `callvalue` guard, then `SLOAD 2` and `RETURN`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem totalSharesBody_eq : totalSharesTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.storage tsRef]] := by rfl

/-- `totalShares()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem wrapperTotalSharesBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 0)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 0) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := wrapperReachTotalSharesBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some totalSharesTransition := wrapperDispatch_totalShares hsel
  have hdec : config.externalABI.decodeCalldata? (totalSharesTransition.params.map Param.name)
      (transitionSignature totalSharesTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, totalSharesTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := wrapperBlocks.wrapper_block_1740_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := wrapperBlocks.wrapper_block_1745 (by simp) rd1
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (wrapperDispatchMem 1) 64
        (by rw [dispatchMem_size 1 (by decide)]; exact lt_usize _ (by decide)), slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ totalSharesTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [uint256Value (solcSlotWordAt (UInt256.ofNat 2) σ I)])) (restrictImmutables contract imms) := by
      rw [totalSharesBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      rw [evalTsRead imms ∅ _ (by simp), storageLoad_initState_ofUInt256_solcSlotWordAt]
    exact rd2.reEquivExecution hcode' hd hdec hbody (returnEquiv_of_encode (uint256ReturnEncoding _))
  · have rd1 := wrapperBlocks.wrapper_block_1740_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [totalSharesBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperWrapper
