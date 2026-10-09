import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.EmptyTupleDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometApproveResponse {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray} {aw ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {z : Bool} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hb : ptr.toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨5226⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: R) mem aw out σ k C) :
    if z then RDret (deployedRuntime v) g s0 σ ByteArray.empty
      else RDrev (deployedRuntime v) g s0 := by
  cases z with
  | false =>
      have r1 := cometWithExtendedAssetList_block_5226_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have r2 := cometWithExtendedAssetList_block_5259
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      exact cometWithExtendedAssetList_block_7166 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 4 ≤ 1024; omega)
        (by change 0 + out.size % UInt256.size ≤ out.size
            simpa using Nat.mod_le out.size UInt256.size) r2
  | true =>
      have r1 := cometWithExtendedAssetList_block_5226_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by decide) h
      have r2 := cometWithExtendedAssetList_block_5232_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega)
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := cometWithExtendedAssetList_block_5238
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      obtain ⟨aw4, k4, C4, r4⟩ := cometAllocateBounded (v := v) (bound := 0)
        (by change R.length + 2 + 6 ≤ 1024; omega) (by decide) (by simpa using hb)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      obtain ⟨k5, C5, r7⟩ := cometDecodeEmptyTuple (v := v)
        (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
      exact cometWithExtendedAssetList_block_22 (immWords := wordsOf (immStore v))
        (by omega) r7

end Benchmarks.CompoundIII.Comet
