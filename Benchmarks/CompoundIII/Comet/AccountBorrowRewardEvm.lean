import Benchmarks.CompoundIII.Comet.AccountMagnitude
import Benchmarks.CompoundIII.Comet.AccountDeltaEvm
import Benchmarks.CompoundIII.Comet.AccountRewardFinishEvm
import Benchmarks.CompoundIII.Comet.Negate104Evm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccountBorrowReward {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr principal a b c d e : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 23 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hs : SourceState s0 ee σ evm) (hneg : signed104 principal < 0)
    (h : RD (deployedRuntime v) ee g s0 ⟨12003⟩
      (⟨0⟩ :: ptr :: UInt256.signextend (UInt256.ofNat 12) principal ::
        a :: b :: c :: d :: e :: ptr :: R) mem aw rdata σ k C) :
    let reward := accountReward v evm basic principal true
    if AccountRewardValid v evm basic principal true then
      ∃ aw' k' C', UserBasicMemory (accountAccruedMemory mem ptr (basic.accrued + reward)) ptr
          (userBasicWithAccrued basic (basic.accrued + reward)) ∧
        RD (deployedRuntime v) ee g s0 ⟨11931⟩ (a :: b :: c :: d :: e :: ptr :: R)
          (accountAccruedMemory mem ptr (basic.accrued + reward)) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have hcurrent : UInt256.shiftRight
      (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac ↦ ac.storage.getD ⟨0⟩ ⟨0⟩))
      (UInt256.ofNat 192) = accountRewardIndex evm true := by
    rw [accountRewardIndex, hs.storageRead, trackingIndexWord_eq]
    rfl
  obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_12003
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 17 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_12003_stack] at r1
  rw [hcurrent] at r1
  have hd := cometAccountDelta (v := v) (by change R.length + 15 + 8 ≤ 1024; omega)
    hm (accountRewardIndex_lt evm true)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hle : basic.index.toNat ≤ (accountRewardIndex evm true).toNat
  · rw [if_pos hle] at hd
    obtain ⟨_, _, _, r2⟩ := hd
    have r3 := cometWithExtendedAssetList_block_12051 (immWords := wordsOf (immStore v))
      (by change R.length + 11 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    by_cases hmin : -(2^103 : Int) < signed104 principal
    · obtain ⟨_, _, r4⟩ := cometNegate104 (v := v)
        (by change R.length + 14 + 5 ≤ 1024; omega) (le_of_lt hneg) hmin
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have hmag : UInt256.land
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
          (negativePrincipal principal) = negativePrincipal principal := by
        rw [u256_land_comm]
        exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl (accountMagnitude_lt true hmin)
      have r5 := cometWithExtendedAssetList_block_7787 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      simp only [cometWithExtendedAssetList_block_7787_stack, hmag] at r5
      have r6 := cometWithExtendedAssetList_block_8112 (immWords := wordsOf (immStore v))
        (by change R.length + 14 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      have r7 := cometWithExtendedAssetList_block_7787 (immWords := wordsOf (immStore v))
        (by change R.length + 12 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      simp only [cometWithExtendedAssetList_block_7787_stack, hmag] at r7
      have r8 := cometWithExtendedAssetList_block_12057 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
      have hf := cometAccountRewardFinish (v := v) (by omega) hm
        (accountMagnitude_lt true hmin) (accountRewardDelta_lt hle)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r8
      by_cases hv : AccountRewardValid v evm basic principal true
      · rw [if_pos hv]
        rw [if_pos ⟨hv.2.2.1, hv.2.2.2⟩] at hf
        obtain ⟨_, _, _, hm', r9⟩ := hf
        have r10 := cometWithExtendedAssetList_block_12062 (immWords := wordsOf (immStore v))
          (by change R.length + 6 + 1 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r9
        exact ⟨_, _, _, hm', r10⟩
      · rw [if_neg hv]
        rw [if_neg (fun h ↦ hv ⟨hle, hmin, h.1, h.2⟩)] at hf
        exact hf
    · rw [if_neg (fun h ↦ hmin h.2.1)]
      have hb := signed104_bounds principal
      exact cometNegate104_revert (v := v)
        (by change R.length + 14 + 5 ≤ 1024; omega) (by omega) r3
  · rw [if_neg hle] at hd
    rw [if_neg (fun h ↦ hle h.1)]
    exact hd

end Benchmarks.CompoundIII.Comet
