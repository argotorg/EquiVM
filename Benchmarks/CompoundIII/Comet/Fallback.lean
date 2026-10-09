import Benchmarks.CompoundIII.Comet.FallbackDispatch
import Benchmarks.CompoundIII.Comet.FallbackEvm
import Benchmarks.CompoundIII.Comet.FallbackSource
import Solm.Refine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometFallbackRefines {σ σ₀ A I} {g : UInt256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 68 → (cometWithExtendedAssetListSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  obtain ⟨k, C, rd⟩ := cometFallbackDispatch (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsize hnm
  obtain ⟨evm', σ', z, out, hc, hs, hr⟩ := cometFallbackRun (by decide) hsize SourceState.init rd
  have hb := cometFallbackSource hc
  have hd := cometFallbackNoSelector hnm
  have hreceive := cometFallbackNoReceive I.calldata
  cases z with
  | false =>
    exact hr.reEquivElim hcode fun _ _ hxi ↦
      .execution hxi (.fallback hd hreceive contract_fallback rfl rfl rfl hb) (.revert rfl rfl)
  | true =>
    obtain hoog | ⟨s, hX, hacc⟩ := hr
    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
    · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
      exact .execution hxi (.fallback hd hreceive contract_fallback rfl rfl rfl hb)
        (.success rfl rfl (hacc.trans hs.accounts) (.rawBytes rfl))

end Benchmarks.CompoundIII.Comet
