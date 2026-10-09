import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometDynamicReturn {v : CometWithExtendedAssetListImmutables}
    {ee g s0 ret R result} (hstack : R.length + 1 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : internalDynamicRun (deployedRuntime v) ee g s0 ⟨3121⟩ (ret :: R) result) :
    internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  cases result with
  | reverted => exact h
  | staticViolation => exact h
  | ok evm =>
    obtain ⟨σ, mem, aw, rdata, k, C, hs, hr⟩ := h
    exact ⟨σ, mem, aw, rdata, _, _, hs,
      cometWithExtendedAssetList_block_3121 (immWords := wordsOf (immStore v)) hstack hret hr⟩

end Benchmarks.CompoundIII.Comet
