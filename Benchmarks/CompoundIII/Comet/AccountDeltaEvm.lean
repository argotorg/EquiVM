import Benchmarks.CompoundIII.Comet.UserBasicMemory
import Benchmarks.CompoundIII.Comet.CheckedSub64Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccountDelta {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr current ret : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hc : current.toNat < 2^64) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11793⟩
      (current :: ⟨32⟩ :: ⟨11801⟩ :: ptr :: ⟨10587⟩ :: ret :: R) mem aw rdata σ k C) :
    if basic.index.toNat ≤ current.toNat then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub current basic.index :: R)
        mem aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_11793 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_11793_stack] at r1
  rw [hm.index] at r1
  have r2 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [cometWithExtendedAssetList_block_2959_stack, mask64Clean _ basic.index_lt] at r2
  have r3 := cometWithExtendedAssetList_block_11801 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hr := cometCheckedSub64 (v := v) (by change R.length + 1 + 6 ≤ 1024; omega)
    hc basic.index_lt (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  split_ifs with hle
  · rw [if_pos hle] at hr
    obtain ⟨_, _, r4⟩ := hr
    have hd : (UInt256.sub current basic.index).toNat < 2^64 := by
      rw [usub_toNat hle]; omega
    have r5 := cometWithExtendedAssetList_block_10587 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
      (by omega) hret r5
    simp only [cometWithExtendedAssetList_block_2959_stack, mask64Clean _ hd] at r6
    exact ⟨_, _, _, r6⟩
  · rw [if_neg hle] at hr
    exact hr

end Benchmarks.CompoundIII.Comet
