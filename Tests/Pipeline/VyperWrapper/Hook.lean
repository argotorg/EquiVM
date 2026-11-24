import Tests.Pipeline.VyperWrapper.Helpers

variable {fork : Ethereum.Fork}

/-!
# Wrapper `hook()`

Dispatcher bucket 3, arm entry pc 198: the `callvalue` guard, then `SLOAD 0` and `RETURN` of the
raw word (the spec's `address` view agrees under `storageWF`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

theorem hookBody_eq : hookTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.storage hookRef]] := by rfl

/-- `hook()`: the theorem `Correct.lean` routes selector 2 to. -/
theorem wrapperHookBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed wrapperBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (wrapperSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (wrapperSelBytes 2) rfl hsel
  have hcode' : I.code = wrapperBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨_, _, rd⟩ := wrapperReachHookBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some hookTransition :=
    wrapperDispatch_hook (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (hookTransition.params.map Param.name)
      (transitionSignature hookTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, hookTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := wrapperBlocks.wrapper_block_198_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := wrapperBlocks.wrapper_block_203 (by simp) rd1
    rw [ulit_toNat' 64 (by decide), ulit_toNat' 32 (by decide),
      toByteArray_write_read_back_of_gap _ (wrapperDispatchMem 3) 64
        (by rw [dispatchMem_size 3 (by decide)]; exact lt_usize _ (by decide)), slotWord_eq] at rd2
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ hookTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [.address (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat)])) (restrictImmutables contract imms) := by
      rw [hookBody_eq]
      refine ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns ?_)
      rw [evalHookRead imms ∅ _ (by simp), storageLoad_initState_ofUInt256_solcSlotWordAt]
    exact rd2.reEquivExecution hcode' hd hdec hbody
      (returnEquiv_of_encode (by
        rw [addressReturnEncoding]
        show some (UInt256.ofNat (AccountAddress.ofNat (solcSlotWordAt ⟨0⟩ σ I).toNat).val).toByteArray = _
        rw [word_roundtrip hwf.1]))
  · have rd1 := wrapperBlocks.wrapper_block_198_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := wrapperBlocks.wrapper_block_1760 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [hookBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperWrapper
