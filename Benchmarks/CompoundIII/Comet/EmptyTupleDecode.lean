import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_028
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometDecodeEmptyTuple {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨5253⟩ (ptr :: ret :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw out σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_5253 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_1465_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [u256_sub_self]; rfl) r1
  have r3 := cometWithExtendedAssetList_block_1475 (immWords := wordsOf (immStore v))
    (by omega) hret r2
  exact ⟨_, _, r3⟩

end Benchmarks.CompoundIII.Comet
