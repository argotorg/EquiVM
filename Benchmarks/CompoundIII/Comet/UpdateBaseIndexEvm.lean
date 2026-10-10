import Benchmarks.CompoundIII.Comet.UpdateBaseModel
import Benchmarks.CompoundIII.Comet.UserBasicMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def accountIndexMemory (mem : ByteArray) (ptr index : UInt256) : ByteArray :=
  writeWord mem (ptr + UInt256.ofNat 32).toNat index

theorem cometUpdateBaseIndex {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr principal a b : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨11931⟩
      (principal :: ⟨0⟩ :: ⟨0⟩ :: a :: b :: ptr :: R) mem aw rdata σ k C) :
    let index := accountRewardIndex evm (principalBorrow principal)
    ∃ aw' k' C', UserBasicMemory (accountIndexMemory mem ptr index) ptr
        (basicSetIndex evm basic principal) ∧
      RD (deployedRuntime v) ee g s0 ⟨11973⟩ (a :: b :: ptr :: R)
        (accountIndexMemory mem ptr index) aw' rdata σ k' C' := by
  dsimp only
  by_cases hn : signed104 principal < 0
  · have hb : principalBorrow principal = true := by simp [principalBorrow, hn]
    rw [hb]
    have r1 := cometWithExtendedAssetList_block_11931_taken (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 3 ≤ 1024; omega) (signed104_slt_neg hn)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_11985 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hcurrent : UInt256.shiftRight
        (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac ↦ ac.storage.getD ⟨0⟩ ⟨0⟩))
        (UInt256.ofNat 192) = accountRewardIndex evm true := by
      rw [accountRewardIndex, hs.storageRead, trackingIndexWord_eq]; rfl
    dsimp only [cometWithExtendedAssetList_block_11985_stack] at r2
    rw [hcurrent] at r2
    have r3 := cometWithExtendedAssetList_block_11957 (immWords := wordsOf (immStore v)) hstack
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [cometWithExtendedAssetList_block_11957_memory,
      mask64Clean _ (accountRewardIndex_lt evm true)] at r3
    have r4 := cometWithExtendedAssetList_block_11998 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    refine ⟨_, _, _, ?_, r4⟩
    simp only [basicSetIndex, hb]
    exact hm.writeIndex _ (accountRewardIndex_lt evm true)
  · have hb : principalBorrow principal = false := by simp [principalBorrow, hn]
    rw [hb]
    have r1 := cometWithExtendedAssetList_block_11931_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 3 ≤ 1024; omega) (signed104_slt_nonneg (by omega)) h
    obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_11940 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 5 ≤ 1024; omega) r1
    have hcurrent : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
        (UInt256.shiftRight (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac ↦ ac.storage.getD ⟨0⟩ ⟨0⟩))
          (UInt256.ofNat 128)) = accountRewardIndex evm false := by
      rw [accountRewardIndex, hs.storageRead, trackingIndexWord_eq]
      exact u256_land_comm _ _
    dsimp only [cometWithExtendedAssetList_block_11940_stack] at r2
    rw [hcurrent] at r2
    have r3 := cometWithExtendedAssetList_block_11957 (immWords := wordsOf (immStore v)) hstack
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [cometWithExtendedAssetList_block_11957_memory,
      mask64Clean _ (accountRewardIndex_lt evm false)] at r3
    refine ⟨_, _, _, ?_, r3⟩
    simp only [basicSetIndex, hb]
    exact hm.writeIndex _ (accountRewardIndex_lt evm false)

end Benchmarks.CompoundIII.Comet
