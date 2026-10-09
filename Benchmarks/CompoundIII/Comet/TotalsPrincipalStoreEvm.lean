import Benchmarks.CompoundIII.Comet.TotalsPrincipalWrite
import Benchmarks.CompoundIII.Comet.InternalOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometStoreTotalsPrincipal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw value ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 7 ≤ 1024) (hperm : evm.executionEnv.perm = true)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (if borrow then ⟨12377⟩ else ⟨12322⟩)
      (UInt256.ofNat 1 :: value :: ret :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ret R
      (.ok (storeTotalsPrincipal evm borrow value)) := by
  have hp : ee.perm = true := by rw [← hs.env]; exact hperm
  cases borrow
  · obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_12322
      (immWords := wordsOf (immStore v)) hstack hp hret h
    exact ⟨_, k', C', sourceState_storeTotalsPrincipal hs false value, hr⟩
  · obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_12377
      (immWords := wordsOf (immStore v)) hstack hp hret h
    exact ⟨_, k', C', sourceState_storeTotalsPrincipal hs true value, hr⟩

end Benchmarks.CompoundIII.Comet
