import Benchmarks.CompoundIII.Comet.ConstructorNonpayable
import Benchmarks.CompoundIII.Comet.ConstructorInitialCalls
import Benchmarks.CompoundIII.Comet.ConstructorInitialImms
import Benchmarks.CompoundIII.Comet.ConstructorScaleEvm
import Benchmarks.CompoundIII.Comet.ConstructorScaleSource
import Benchmarks.CompoundIII.Comet.ConstructorRemainingImmsEvm
import Benchmarks.CompoundIII.Comet.ConstructorRemainingImmsSource
import Benchmarks.CompoundIII.Comet.ConstructorFactoryMemory
import Benchmarks.CompoundIII.Comet.ConstructorAssetsCall
import Benchmarks.CompoundIII.Comet.ConstructorAssetsSource
import Benchmarks.CompoundIII.Comet.ConstructorRuntimeFinish
import Solm.RefineWithCodeBound

/-!
# CometWithExtendedAssetList constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000 in
theorem cometWithExtendedAssetListConstructorCorrect :
    typedConstructorRefinementWithCodeBound config cometWithExtendedAssetListCreationBytecode
      contract (immutableLayout.deployed cometWithExtendedAssetListBytecode) := by
  intro σ σ₀ g A I args code hdeploy hcode hcalldata hperm hsize
  by_cases hv : I.weiValue = ⟨0⟩
  · obtain ⟨c, rfl, hinitcode, hbound⟩ := cometConstructorBoundedInput hdeploy hcode hsize
    rcases cometConstructorInitialCalls (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
      hinitcode hv hbound with hdone | ⟨evm', σ', out, feed, aw, k, C, hfree, hvalid, hs,
        hhi, hlo, hdecimals, hfhi, hflo, hfeed, hsource, hevm⟩
    · exact hdone
    · have hm := ConstructorDataMemory.priceFeed hfree
        (by change out.size < 2^256; omega) (by change feed.size < 2^256; omega)
      obtain ⟨aw', k', C', hevm'⟩ := cometConstructorInitialImms
        (by change 15 ≤ 1024; decide) hm hbound hevm
      have hsource' := constructorSourceInitialImms_exec hdecimals hsource
      have hm' := constructorInitialImmMemory_data hm (calldataWord out 0)
      have hscale := cometConstructorScale (by change 14 ≤ 1024; decide) hdecimals hm' hbound hevm'
      by_cases hscaleLo : 6 ≤ (calldataWord out 0).toNat
      · rw [if_pos hscaleLo] at hscale
        obtain ⟨aw'', k'', C'', hevm''⟩ := hscale
        have hsource'' := constructorSourceScaleChecked_exec hdecimals hscaleLo hsource'
        have hm'' := constructorScaleMemory_data hm' (calldataWord out 0)
        have hptr : memLoad (UInt256.ofNat 64)
            (constructorScaleMemory c (calldataWord out 0)
              (constructorInitialImmMemory c (calldataWord out 0)
                (constructorPriceFeedReturnMemory c out feed))) =
            UInt256.ofNat (constructorAssetFree c c.assetConfigs.length + 64) := by
          rw [constructorScaleInitialMemory_free (by
            unfold constructorPriceFeedReturnMemory
            rw [writeWord_sparse_size]
            omega)]
          exact memLoad_writeWord_self _ (UInt256.ofNat 64) _
        obtain ⟨aw3, k3, C3, hevm3⟩ := cometConstructorRemainingImms
          (by change 23 ≤ 1024; decide) hm'' (constructorScaleMemory_scale _ _ _)
          (constructorScaleInitialMemory_delegate _ _ _) hptr hbound hvalid.2.1 hevm''
        have hsource3 := constructorSourceDelegate_exec
          (constructorSourceRemainingImms_exec hdecimals hvalid.2.1 hsource'')
        have houtsize : out.size < UInt256.size := by change _ < 2^256; omega
        have hfeedsize : feed.size < UInt256.size := by change _ < 2^256; omega
        obtain ⟨evm4, σ4, z, factoryOut, aw4, k4, C4, hcall4, hs4, hhi4, hevm4⟩ :=
          cometConstructorFactoryCall (by change 17 ≤ 1024; decide) hs
            (constructorFactoryInputMemory_payload hvalid.2.1 houtsize hfeedsize) hevm3
        have hresponse := cometConstructorFactoryResponse (by change 21 ≤ 1024; decide)
          (by rw [constructorFactoryInputMemory_size hvalid.2.1 houtsize hfeedsize])
          (constructorFactoryPtr_ge hvalid.2.1) (constructorFactoryPtr_fits hvalid.2.1) hhi4 hevm4
        by_cases hfactory : z = true ∧ ConstructorFactoryReturnValid factoryOut
        · rw [if_pos hfactory] at hresponse
          obtain ⟨aw5, k5, C5, hevm5⟩ := hresponse
          rcases hfactory with ⟨rfl, hfactory⟩
          have hsource4 := constructorSourceFactory_exec hsource3 hcall4 (by omega) hfactory
          obtain ⟨evm6, σ6, z6, assetOut, aw6, k6, C6, hcall6, hs6, hhi6, hevm6⟩ :=
            cometConstructorAssetsCall (by change 23 ≤ 1024; decide) hs4 hperm hvalid.2.1
              houtsize hfeedsize hhi4 hfactory.2 hevm5
          have hassetsFit := constructorAssetsPtr_fits hvalid.2.1
          have hresponse6 := cometCreateAssetListResponse (by change 20 ≤ 1024; decide)
            (by
              rw [constructorAssetsPtr_toNat hvalid.2.1]
              have hm := constructorAssetsInputMemory_size (w := calldataWord out 0)
                (out := out) (feed := feed) (factoryOut := factoryOut) hvalid.2.1
              omega)
            (by
              rw [constructorAssetsPtr_toNat hvalid.2.1]
              unfold constructorAssetsPtr
              omega)
            (by rw [constructorAssetsPtr_toNat hvalid.2.1]; omega) hhi6 hevm6
          have hn : c.assetConfigs.length < UInt256.size := by omega
          by_cases hassets : z6 = true ∧ ConstructorFactoryReturnValid assetOut
          · rw [if_pos hassets] at hresponse6
            obtain ⟨aw7, k7, C7, hevm7⟩ := hresponse6
            rcases hassets with ⟨rfl, hassets⟩
            have hsource6 := constructorSourceAssets_exec hn hsource4 hcall6 (by omega) hassets
            have hret := cometConstructorDeployReturn (by change 15 ≤ 1024; decide)
              hvalid.2.1 hdecimals hassets.2 houtsize hfeedsize
              (by change _ < 2^256; omega) (by change _ < 2^256; omega) hevm7
            obtain hoog | ⟨sf, hX, hacc⟩ := hret
            · exact .outOfGas (Xi_error_of_X (g := g) (by
                rw [← hinitcode] at hoog; exact hoog))
            · have hxi := Xi_success_of_X (g := g) (by rw [← hinitcode] at hX; exact hX)
              rw [hacc] at hxi
              exact .execution hxi
                (.intro rfl rfl (constructorSourceArgs_bind c) (.execBlockOK hsource6))
                (.success rfl rfl hs6.accounts rfl)
                (constructorFinalImms_fit hdecimals hvalid.2.1)
          · rw [if_neg hassets] at hresponse6
            apply cometConstructorRevert hinitcode hresponse6
            exact .intro rfl rfl (constructorSourceArgs_bind c)
              (.execBlockRevert (constructorSourceAssets_revert hn hsource4 hcall6
                (by omega) hassets))
        · rw [if_neg hfactory] at hresponse
          apply cometConstructorRevert hinitcode hresponse
          exact .intro rfl rfl (constructorSourceArgs_bind c)
            (.execBlockRevert (constructorSourceFactory_revert hsource3 hcall4 (by omega) hfactory))
      · rw [if_neg hscaleLo] at hscale
        apply cometConstructorRevert hinitcode hscale
        exact .intro rfl rfl (constructorSourceArgs_bind c)
          (.execBlockRevert (constructorSourceScaleChecked_revert hdecimals hscaleLo hsource'))
  · exact cometConstructorNonpayable hdeploy hcode hv

end Benchmarks.CompoundIII.Comet
