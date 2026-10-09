import Benchmarks.Safe.GuardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- Common final refinement step for both guard setters, after the interface check succeeds.
theorem guardFinish {kind : GuardKind} {σ σ₀ σ' : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} {guard : UInt256} {evm' : EVM.State} {locals : Store}
    (hcode : I.code = safeBytecode)
    (hd : selectorDispatchMsg contract I.calldata = some (guardTransition kind))
    (hdec : decodeCalldataWithMode config.abiDecodeMode
      ((guardTransition kind).params.map Param.name)
      (transitionSignature (guardTransition kind)).paramTypes I.calldata =
      some (guardArgs kind guard))
    (hc : guard.toNat < EVM.addressModulus) (hv : I.weiValue = ⟨0⟩)
    (ha : I.source = I.codeOwner)
    (hg : locals[guardName kind]? = some (.address (AccountAddress.ofNat guard.toNat)))
    (hb : locals.get? (guardField kind) = none) (hee : evm'.executionEnv = I)
    (hacc : evm'.accountMap = σ')
    (hcheck : ExecStmt config (guardFrame kind guard) (initState σ σ₀ (.ofUInt256 g) A I)
      (guardCheck kind) (.ok { contract := contract, locals := locals } evm'))
    (hstatic : I.perm = false → RDstatic safeBytecode (.ofUInt256 g)
      (initState σ σ₀ (.ofUInt256 g) A I))
    (hret : I.perm = true → RDret safeBytecode (.ofUInt256 g)
      (initState σ σ₀ (.ofUInt256 g) A I)
      (sstoreAccountMap I.codeOwner σ' (guardStorageSlot kind) guard) ByteArray.empty) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  cases hp : I.perm with
  | false =>
      have hbody := safeGuardSourceStatic hc hv ha hg hb (by rw [hee]; exact hp) hcheck
      exact RDstatic.reEquivElim hcode (hstatic hp) fun hΞ ↦
        reEquivSelectorExecution hd hdec hbody (.staticHalt hΞ rfl)
  | true =>
      have hbody := safeGuardSourceSuccess hc hv ha hg hb hcheck
      refine reEquivReturnElim hcode (hret hp) fun _ _ hsuccess ↦ ?_
      refine reEquivSelectorExecution hd hdec hbody
        (.success hsuccess rfl (by simp only [storageStore_accountMap, hee, hacc]) ?_)
      have hty : (guardTransition kind).returnType = [] := by cases kind <;> rfl
      rw [hty]
      exact .abi (.fallthrough rfl rfl encodeReturnValues_nil)

end Benchmarks.Safe
