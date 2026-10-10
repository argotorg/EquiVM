import Benchmarks.CompoundIII.Comet.ConstructorFirstPhase
import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedCheck
import Benchmarks.CompoundIII.Comet.ConstructorPriceFeedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

/-- Decode the constructor input, check its configuration and complete both decimals calls.
    Every failing branch already establishes full constructor refinement by reverting. -/
theorem cometConstructorInitialCalls {σ σ₀ A I} {g : UInt256} {c : ConstructorConfig}
    (hcode : I.code = cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
    (hv : I.weiValue = ⟨0⟩) (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
      (immutableLayout.deployed cometWithExtendedAssetListBytecode) ∨
    ∃ evm' σ' out feed aw k C,
      constructorAssetFree c c.assetConfigs.length < 2^64 ∧ ConstructorChecksValid c ∧
      SourceState (initState σ σ₀ (Sat256.ofUInt256 g) A I) I σ' evm' ∧
      out.size < 2^138 ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 18 ∧
      feed.size < 2^138 ∧ 32 ≤ feed.size ∧ calldataWord feed 0 = ⟨8⟩ ∧
      ExecBlock config (constructorSourceEntry c) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (contract.ctor.body.take 9)
        (.ok (constructorSourcePriceFeed c (calldataWord out 0) (calldataWord feed 0)) evm') ∧
      RD (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray) I
        (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨902⟩
        (calldataWord out 0 :: UInt256.ofNat (constructorRecordBase c) ::
          constructorAssetLoopStack c c.assetConfigs.length)
        (constructorPriceFeedReturnMemory c out feed) aw feed σ' k C := by
  rcases cometConstructorFirstPhase (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hv hsize with
    hdone | ⟨evm', σ', out, aw, k, C, hfree, hs, ho, hlo, hdecimals, hsource, hevm⟩
  · exact Or.inl hdone
  · have hout : out.size < UInt256.size := by change _ < 2^256; omega
    have hchecks := cometConstructorChecks hsize hfree hout hevm
    by_cases hvalid : ConstructorChecksValid c
    · rw [if_pos hvalid] at hchecks
      obtain ⟨_, _, _, hchecks⟩ := hchecks
      have hsource' := constructorSourceChecks_exec hsource hvalid
      obtain ⟨_, _, _, henter⟩ := cometConstructorPriceFeedEnter hsize hfree hout hchecks
      obtain ⟨evm'', σ'', z, feed, _, _, _, hc, hs', hf, hcall⟩ :=
        cometConstructorPriceFeedCall hfree hout hs henter
      have finish
          (hr : RDrev (cometWithExtendedAssetListCreationBytecode ++ c.encodedArgs.toByteArray)
            (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I))
          (hbad : ¬ (z = true ∧ 32 ≤ feed.size ∧ calldataWord feed 0 = ⟨8⟩)) :
          typedConstructorRefinementFor config contract [c.value] σ σ₀ g A I
            (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
        apply cometConstructorRevert hcode hr
        refine .intro rfl rfl (constructorSourceArgs_bind c) (.execBlockRevert ?_)
        exact constructorSourcePriceFeedChecked_revert hsource' hc (by omega) hbad
      have hresponse := cometConstructorPriceFeedResponse hfree hout hf hcall
      by_cases hdecode : z = true ∧ DecimalsReturnValid feed
      · rw [if_pos hdecode] at hresponse
        obtain ⟨_, _, _, hresponse⟩ := hresponse
        have hcheck := cometConstructorPriceFeedCheck hdecode.2.2 hresponse
        by_cases hword : calldataWord feed 0 = ⟨8⟩
        · rw [if_pos hword] at hcheck
          obtain ⟨aw', k', C', hcheck⟩ := hcheck
          right
          refine ⟨evm'', σ'', out, feed, aw', k', C', hfree, hvalid, hs', ho, hlo,
            hdecimals, hf, hdecode.2.1, hword, ?_, hcheck⟩
          have hc' := hc
          rw [hdecode.1] at hc'
          exact constructorSourcePriceFeedChecked_exec hsource' hc' (by omega) hdecode.2.1 hword
        · rw [if_neg hword] at hcheck
          exact Or.inl (finish hcheck (fun hh ↦ hword hh.2.2))
      · rw [if_neg hdecode] at hresponse
        exact Or.inl (finish hresponse (fun hh ↦ hdecode ⟨hh.1, hh.2.1, by rw [hh.2.2]; decide⟩))
    · rw [if_neg hvalid] at hchecks
      left
      apply cometConstructorRevert hcode hchecks
      exact .intro rfl rfl (constructorSourceArgs_bind c)
        (.execBlockRevert (constructorSourceChecks_revert hsource hvalid))

end Benchmarks.CompoundIII.Comet
