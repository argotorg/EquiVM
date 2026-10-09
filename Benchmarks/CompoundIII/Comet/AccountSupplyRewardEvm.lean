import Benchmarks.CompoundIII.Comet.AccountMagnitude
import Benchmarks.CompoundIII.Comet.AccountDeltaEvm
import Benchmarks.CompoundIII.Comet.AccountRewardFinishEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccountSupplyReward {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr principal a b c d e : UInt256}
    {basic : UserBasicData} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hs : SourceState s0 ee σ evm) (hpos : 0 ≤ signed104 principal)
    (h : RD (deployedRuntime v) ee g s0 ⟨11746⟩
      (⟨0⟩ :: ptr :: UInt256.signextend (UInt256.ofNat 12) principal ::
        a :: b :: c :: d :: e :: ptr :: R) mem aw rdata σ k C) :
    let reward := accountReward v evm basic principal false
    if AccountRewardValid v evm basic principal false then
      ∃ aw' k' C', UserBasicMemory (accountAccruedMemory mem ptr (basic.accrued + reward)) ptr
          (userBasicWithAccrued basic (basic.accrued + reward)) ∧
        RD (deployedRuntime v) ee g s0 ⟨11931⟩ (a :: b :: c :: d :: e :: ptr :: R)
          (accountAccruedMemory mem ptr (basic.accrued + reward)) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  have hmin : -(2^103 : Int) < signed104 principal := by omega
  have hcurrent : UInt256.land
      (UInt256.shiftRight (σ.get? ee.codeOwner |>.option ⟨0⟩ (fun ac ↦ ac.storage.getD ⟨0⟩ ⟨0⟩))
        (UInt256.ofNat 128))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      accountRewardIndex evm false := by
    rw [accountRewardIndex, hs.storageRead, trackingIndexWord_eq]
    rfl
  obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_11746
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 16 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_11746_stack] at r1
  rw [hcurrent] at r1
  have hd := cometAccountDelta (v := v) (by change R.length + 12 + 8 ≤ 1024; omega)
    hm (accountRewardIndex_lt evm false)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  by_cases hle : basic.index.toNat ≤ (accountRewardIndex evm false).toNat
  · rw [if_pos hle] at hd
    obtain ⟨_, _, _, r2⟩ := hd
    have r3 := cometWithExtendedAssetList_block_11807 (immWords := wordsOf (immStore v))
      (by change R.length + 11 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have hmag : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
        (UInt256.signextend (UInt256.ofNat 12) principal) = positivePrincipal principal := by
      rw [show UInt256.signextend (UInt256.ofNat 12) principal = positivePrincipal principal
        from signextend104_nonneg hpos, u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (bits := 104) rfl
        (accountMagnitude_lt false hmin)
    simp only [cometWithExtendedAssetList_block_11807_stack, hmag] at r3
    have hf := cometAccountRewardFinish (v := v) (by omega) hm
      (accountMagnitude_lt false hmin) (accountRewardDelta_lt hle)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    by_cases hv : AccountRewardValid v evm basic principal false
    · rw [if_pos hv, if_pos ⟨hv.2.2.1, hv.2.2.2⟩] at *
      exact hf
    · rw [if_neg hv]
      rw [if_neg (fun h ↦ hv ⟨hle, hmin, h.1, h.2⟩)] at hf
      exact hf
  · rw [if_neg hle] at hd
    rw [if_neg (fun h ↦ hle h.1)]
    exact hd

end Benchmarks.CompoundIII.Comet
