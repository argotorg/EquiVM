import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_042
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedSub256 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8603⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    if y.toNat ≤ x.toNat then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  split_ifs with hle
  · have r1 := cometWithExtendedAssetList_block_8603_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (ult_zero hle) h
    have r2 := cometWithExtendedAssetList_block_8611 (immWords := wordsOf (immStore v))
      (by omega) hret r1
    exact ⟨_, _, r2⟩
  · have r1 := cometWithExtendedAssetList_block_8603_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_7775 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    exact cometWithExtendedAssetList_block_7730 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 2 ≤ 1024; omega) r2

end Benchmarks.CompoundIII.Comet
