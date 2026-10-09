import Benchmarks.CompoundIII.Comet.ConstructorSourceChecks

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Supply an actual EVM-call outcome for the source's unconditional-reversion proof.
    The witness uses the input state's available gas; no particular return value is assumed. -/
theorem constructorDecimalsSource_exists (evm : EVM.State) (asset : AccountAddress) :
    ∃ evm' z out,
      callViaEVM evm asset 0 decimalsPayload (z, evm', out) false ∧ out.size < 2^138 := by
  by_cases hd : evm.executionEnv.depth = 1024
  · refine ⟨{ evm with substate := (evm.addAccessedAccount asset).substate },
      false, ByteArray.empty, ?_, by decide⟩
    exact callViaEVM.callNotMade rfl rfl (fun h ↦ h.2 hd)
  · let result := Θ evm.accountMap evm.σ₀ (evm.addAccessedAccount asset).substate
      evm.executionEnv.codeOwner evm.executionEnv.sender asset (toExecute evm.accountMap asset)
      evm.machineState.gasAvailable.toUInt256 (UInt256.ofNat evm.executionEnv.gasPrice)
      ⟨0⟩ ⟨0⟩ decimalsPayload (evm.executionEnv.depth + 1) evm.executionEnv.header
      evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks false
    have hθ : result = Θ evm.accountMap evm.σ₀ (evm.addAccessedAccount asset).substate
        evm.executionEnv.codeOwner evm.executionEnv.sender asset (toExecute evm.accountMap asset)
        evm.machineState.gasAvailable.toUInt256 (UInt256.ofNat evm.executionEnv.gasPrice)
        ⟨0⟩ ⟨0⟩ decimalsPayload (evm.executionEnv.depth + 1) evm.executionEnv.header
        evm.executionEnv.blobVersionedHashes evm.executionEnv.blocks false := rfl
    obtain ⟨σ', gas', A', z, out⟩ := result
    refine ⟨{ evm with accountMap := σ', substate := A' }, z, out, ?_, ?_⟩
    · apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := gas') (A' := A')
        wordOfInt_zero.symm ?_ rfl (Fin.zero_le _) hd
      exact ⟨evm.machineState.gasAvailable.toUInt256, (evm.addAccessedAccount asset).substate, hθ⟩
    · exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hθ
        (by change 4 ≤ _; decide)

theorem cometConstructorOversized_source {σ σ₀ A I} {g : UInt256} {c : ConstructorConfig}
    (hv : I.weiValue = ⟨0⟩) (hn : 24 < c.assetConfigs.length) :
    solmCtorExec config contract [c.value] σ σ₀ g A I .reverted := by
  obtain ⟨evm', z, out, hc, ho⟩ :=
    constructorDecimalsSource_exists (initState σ σ₀ (Sat256.ofUInt256 g) A I) c.baseToken
  refine .intro rfl rfl (constructorSourceArgs_bind c) (.execBlockRevert ?_)
  exact constructorSourceOversized_revert hv hc (by omega) hn

/-- Match an EVM constructor revert with a proved source constructor revert. -/
theorem cometConstructorRevert {σ σ₀ A I} {g : UInt256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hevm : RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
      (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hsource : solmCtorExec config contract [c.value] σ σ₀ g A I .reverted) :
    typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
      (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
  obtain hoog | ⟨s, out, hX⟩ := hevm
  · exact .outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_revert_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    exact .execution hxi hsource (.revert rfl rfl) trivial

theorem cometConstructorAllocationFailure {σ σ₀ A I} {g : UInt256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hfree : ¬ constructorAssetFree c c.assetConfigs.length < 2^64) :
    typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
      (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
  have hd := cometConstructorDecode (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
    hcode hv hsize
  rw [if_neg hfree] at hd
  apply cometConstructorRevert hcode hd
  apply cometConstructorOversized_source hv
  unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase
    at hfree
  omega

end Benchmarks.CompoundIII.Comet
