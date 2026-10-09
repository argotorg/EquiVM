import Benchmarks.CompoundIII.Comet.UserBasicMemory
import Benchmarks.CompoundIII.Comet.UserBasicLocal
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_041
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def accountAccruedMemory (mem : ByteArray) (ptr accrued : UInt256) : ByteArray :=
  writeWord mem (ptr + UInt256.ofNat 64).toNat accrued

theorem cometAccountRewardAdd {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr reward ret a b c d e : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hr : reward.toNat < 2^64) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11900⟩
      (reward :: ret :: a :: b :: c :: d :: e :: ptr :: R) mem aw rdata σ k C) :
    if basic.accrued.toNat + reward.toNat < 2^64 then
      ∃ aw' k' C', UserBasicMemory (accountAccruedMemory mem ptr (basic.accrued + reward)) ptr
          (userBasicWithAccrued basic (basic.accrued + reward)) ∧
        RD (deployedRuntime v) ee g s0 ret (a :: b :: c :: d :: e :: ptr :: R)
          (accountAccruedMemory mem ptr (basic.accrued + reward)) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_11900 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_11900_stack] at r1
  rw [show memLoad (ptr + UInt256.ofNat 64) mem = basic.accrued from hm.accrued] at r1
  have r2 := cometWithExtendedAssetList_block_2959 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [cometWithExtendedAssetList_block_2959_stack, mask64Clean _ basic.accrued_lt] at r2
  have r3 := cometWithExtendedAssetList_block_8244 (immWords := wordsOf (immStore v))
    (by change R.length + 11 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  split_ifs with hsum
  · have hbound : (basic.accrued + reward).toNat < 2^64 := by
      change (UInt256.add basic.accrued reward).toNat < 2^64
      rw [addWord_toNat _ _ (lt_trans hsum (by decide))]
      exact hsum
    obtain ⟨_, _, r4⟩ := cometCheckedAdd64 (v := v)
      (by change R.length + 8 + 6 ≤ 1024; omega) basic.accrued_lt hr hsum
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    have r5 := cometWithExtendedAssetList_block_11918 (immWords := wordsOf (immStore v))
      (by change R.length + 6 + 6 ≤ 1024; omega) hret r4
    simp only [cometWithExtendedAssetList_block_11918_memory, mask64Clean _ hbound] at r5
    refine ⟨_, _, _, ?_, r5⟩
    rw [userBasicWithAccrued_eq basic _ hbound]
    exact hm.writeAccrued _ hbound
  · exact cometCheckedAdd64_revert (v := v)
      (by change R.length + 9 + 5 ≤ 1024; omega) basic.accrued_lt hr (le_of_not_gt hsum) r3

end Benchmarks.CompoundIII.Comet
