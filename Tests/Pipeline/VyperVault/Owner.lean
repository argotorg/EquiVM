import Tests.Pipeline.VyperVault.Helpers

variable {fork : Ethereum.Fork}

/-!
# VyperVault `owner()`

Dispatcher bucket 8: the callvalue guard at pc 1193, then the `CODECOPY` of the immutable section
and `RETURN` of its single word.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

theorem ownerBody_eq : ownerTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return [.immutable "OWNER"]] := by rfl

/-- `owner()`: the theorem `Correct.lean` routes selector 6 to. -/
theorem vyperVaultOwnerBody {σ σ₀ A I} {g : UInt256} (imms : Store) (hfit : immutablesFit contract imms)
    (hwf : storageWF σ I)
    (hcode : I.code = immutableLayout.deployed vyperVaultBytecode imms) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vyperVaultSelBytes 6)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (restrictImmutables contract imms) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vyperVaultSelBytes 6) rfl hsel
  have hcode' : I.code = vyperVaultBytecode ++ immutableLayout.suffixWords (wordsOf imms) := by
    rw [hcode, deployed_of_fit hfit]
  obtain ⟨a, hget⟩ := owner_of_fit hfit
  obtain ⟨_, _, rd⟩ := vyperVaultReachOwnerBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode' hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some ownerTransition :=
    vyperVaultDispatch_owner (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) hsel
  have hdec : config.externalABI.decodeCalldata? (ownerTransition.params.map Param.name)
      (transitionSignature ownerTransition).paramTypes I.calldata = some ∅ := by
    simpa [config, contract, Syntax.contractSyntax, ownerTransition] using
      (decodeCalldataWithMode_empty_ok (mode := DecodeMode.vyper) (cd := I.calldata) hsz)
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := vyperVaultBlocks.vyperVault_block_1193_fallthrough (by simp) (by simpa using hwv) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1198 (immWords := wordsOf imms) (by simp) rd1
    have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅
        ownerTransition.body
        (.returned (frame imms ∅) (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [.address a]))
        (restrictImmutables contract imms) := by
      rw [ownerBody_eq]
      exact ExecFuncBody.execBlockRet
        ((ABlock.start.requireStep (evalCallvalueEq_true (by simpa [initState] using hwv))).returns
          (evalImmutable_OWNER hget ∅ _))
    exact rd2.reEquivExecution hcode' hd hdec hbody
      (returnEquiv_of_encode (by rw [suffixWords_OWNER, wordsOf_OWNER hget]; exact addressReturnEncoding a))
  · have rd1 := vyperVaultBlocks.vyperVault_block_1193_taken (by simp) (by simpa using hwv)
      (by apply D_J_contains_append_left; jump_dest) rd
    have rd2 := vyperVaultBlocks.vyperVault_block_1403 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode' hd
      (fun _ => by rw [ownerBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2

end Tests.Pipeline.VyperVault
