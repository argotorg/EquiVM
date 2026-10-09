import Benchmarks.CompoundIII.Comet.ConstructorOversized

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Constructor decoding and the first external call either establish refinement by reverting,
    or leave matching source/EVM states after the checked base-token decimals result. -/
theorem cometConstructorFirstPhase {σ σ₀ A I} {g : UInt256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
      (immutableLayout.deployed cometWithExtendedAssetListBytecode) ∨
    ∃ evm' σ' out aw k C,
      constructorAssetFree c c.assetConfigs.length < 2^64 ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      out.size < 2^138 ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 18 ∧
      ExecBlock config (constructorSourceEntry c) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (contract.ctor.body.take 4) (.ok (constructorSourceDecimals c (calldataWord out 0)) evm') ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I
        (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨764⟩
        (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorDecimalsReturnMemory c out) aw out σ' k C := by
  by_cases hfree : constructorAssetFree c c.assetConfigs.length < 2^64
  · have hd := cometConstructorDecodeToDecimals (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hv hsize
    rw [if_pos hfree] at hd
    obtain ⟨_, _, _, hcall⟩ := hd
    obtain ⟨evm', σ', z, out, _, _, _, hc, hs, ho, hr⟩ :=
      cometConstructorDecimalsCall hfree hcall
    have finish
        (hevm : RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
          (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
        (hbad : ¬ (z = true ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 18)) :
        typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
          (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
      apply cometConstructorRevert hcode hevm
      refine .intro rfl rfl (constructorSourceArgs_bind c) (.execBlockRevert ?_)
      exact constructorSourceDecimalsChecked_revert hv hc (by omega) hbad
    have hresponse := cometConstructorDecimalsResponse hfree ho hr
    by_cases hdecode : z = true ∧ DecimalsReturnValid out
    · rw [if_pos hdecode] at hresponse
      obtain ⟨_, _, _, hresponse⟩ := hresponse
      have hcheck := cometConstructorDecimalsCheck hdecode.2.2 hresponse
      by_cases hword : (calldataWord out 0).toNat ≤ 18
      · rw [if_pos hword] at hcheck
        obtain ⟨aw', k', C', hcheck⟩ := hcheck
        right
        refine ⟨evm', σ', out, aw', k', C', hfree, hs, ho, hdecode.2.1, hword, ?_, hcheck⟩
        have hc' := hc
        rw [hdecode.1] at hc'
        exact constructorSourceDecimalsChecked_exec hv hc' (by omega) hdecode.2.1 hword
      · rw [if_neg hword] at hcheck
        exact Or.inl (finish hcheck (fun hh ↦ hword hh.2.2))
    · rw [if_neg hdecode] at hresponse
      exact Or.inl (finish hresponse (fun hh ↦ hdecode ⟨hh.1, hh.2.1, by omega⟩))
  · exact Or.inl (cometConstructorAllocationFailure hcode hv hsize hfree)

end Benchmarks.CompoundIII.Comet
