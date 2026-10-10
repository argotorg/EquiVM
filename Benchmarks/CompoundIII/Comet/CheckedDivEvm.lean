import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedDiv {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨9174⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    if y ≠ ⟨0⟩ then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.div x y :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  split_ifs with hn
  · have r1 := cometWithExtendedAssetList_block_9174_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (isZero_eq_zero_of_ne hn) h
    have r2 := cometWithExtendedAssetList_block_9181
      (immWords := wordsOf (immStore v)) (by omega) hvalid r1
    exact ⟨_, _, r2⟩
  · have hz : y = ⟨0⟩ := not_ne_iff.mp hn
    have r1 := cometWithExtendedAssetList_block_9174_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hz]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_9184
      (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_9151 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
