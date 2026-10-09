import Benchmarks.CompoundIII.Comet.PackedGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometMask128 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw word ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hw : word.toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨2451⟩ (word :: ret :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ret (word :: R) mem aw rdata σ (k + 9) (C + 30) := by
  have hr := cometWithExtendedAssetList_block_2451 (immWords := wordsOf (immStore v))
    hstack hret h
  simpa only [cometWithExtendedAssetList_block_2451_stack, mask128Clean word hw] using hr

end Benchmarks.CompoundIII.Comet
