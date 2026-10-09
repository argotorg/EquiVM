import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.CheckedDivEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometMulFactor {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n factor ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11132⟩ (n :: factor :: ret :: R) mem aw rdata σ k C) :
    if n.toNat * factor.toNat < UInt256.size then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (mulFactorWord n factor :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_11132 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hm : n.toNat * factor.toNat < UInt256.size
  · rw [if_pos hm]
    obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v) (by simpa using hstack) hm
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    exact ⟨_, _, cometWithExtendedAssetList_block_9192
      (immWords := wordsOf (immStore v)) (by omega) hret r2⟩
  · rw [if_neg hm]
    exact cometCheckedMul_revert (v := v) (by simpa using hstack) (le_of_not_gt hm) r1

end Benchmarks.CompoundIII.Comet
