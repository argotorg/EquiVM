import Benchmarks.CompoundIII.Comet.AssetMembershipSelected

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def assetMembershipChangePc (add : Bool) : UInt256 := if add then ⟨14174⟩ else ⟨14339⟩

def assetMembershipChangeStack (add : Bool) (offset : UInt256) (account : AccountAddress)
    (ptr ret : UInt256) (R : List UInt256) : List UInt256 :=
  if add then offset :: EVM.word account.val :: ptr :: ret :: R
  else EVM.word account.val :: ptr :: ret :: R

def AssetMembershipRun (v : CometWithExtendedAssetListImmutables) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (mem rdata : ByteArray) (account : AccountAddress)
    (ret : UInt256) (R : List UInt256) (result : InternalOutcome) : Prop :=
  ∃ mem', (mem' = mem ∨ mem' = twoWordHashMem (EVM.word account.val) ⟨5⟩ mem) ∧
    internalMemoryRun (deployedRuntime v) ee g s0 mem' rdata ret R result

theorem assetMembershipWrite_low (evm : EVM.State) (account : AccountAddress)
    (offset : UInt256) (add : Bool) (ho : offset.toNat < 16) :
    assetMembershipWriteResult evm account offset add =
      assetMembershipFieldResult evm account add false offset.toNat := by
  simp only [assetMembershipWriteResult, if_pos (show offset.toNat < 24 by omega),
    assetMembershipState, if_pos ho, assetMembershipFieldResult,
    Bool.false_eq_true, if_false]

theorem assetMembershipWrite_high (evm : EVM.State) (account : AccountAddress)
    (offset : UInt256) (add : Bool) (hlo : ¬ offset.toNat < 16) (hhi : offset.toNat < 24) :
    assetMembershipWriteResult evm account offset add =
      assetMembershipFieldResult evm account add true (offset.toNat - 16) := by
  simp only [assetMembershipWriteResult, if_pos hhi, assetMembershipState, if_neg hlo,
    assetMembershipFieldResult, if_true]

theorem cometMembershipChange {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw offset ptr ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (add : Bool) (hstack : R.length + 14 ≤ 1024)
    (hoffset : memLoad ptr mem = offset) (ho : offset.toNat < 256)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (assetMembershipChangePc add)
      (assetMembershipChangeStack add offset account ptr ret R) mem aw rdata σ k C) :
    AssetMembershipRun v ee g s0 mem rdata account ret R
      (assetMembershipWriteResult evm account offset add) := by
  have hright : UInt256.land offset (UInt256.ofNat 255) = offset :=
    u256LandMaskCleanOfToNat _ _ (bits := 8) rfl ho
  have hleft : UInt256.land (UInt256.ofNat 255) offset = offset := by
    rw [u256_land_comm, hright]
  cases add
  · by_cases h16 : offset.toNat < 16
    · have r1 := cometWithExtendedAssetList_block_14339_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [hoffset, hleft, ult_one h16]; decide) h
      dsimp only [cometWithExtendedAssetList_block_14339_fallthrough_stack] at r1
      rw [hoffset, hleft] at r1
      refine ⟨_, Or.inr rfl, ?_⟩
      rw [assetMembershipWrite_low evm account offset false h16]
      exact cometMembershipAssets (v := v) account false hstack hoffset h16 hret hs r1
    · have r1 := cometWithExtendedAssetList_block_14339_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [hoffset, hleft, ult_zero (show (UInt256.ofNat 16).toNat ≤ offset.toNat by change 16 ≤ offset.toNat; omega)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_14339_taken_stack] at r1
      rw [hoffset, hleft] at r1
      by_cases h24 : offset.toNat < 24
      · have r2 := cometWithExtendedAssetList_block_14411_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
          (by rw [ult_one h24]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        refine ⟨_, Or.inr rfl, ?_⟩
        rw [assetMembershipWrite_high evm account offset false h16 h24]
        exact cometMembershipReserved (v := v) account false hstack (by omega) h24
          hret hs r2
      · have r2 := cometWithExtendedAssetList_block_14411_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
          (ult_zero (show (UInt256.ofNat 24).toNat ≤ offset.toNat by
            change 24 ≤ offset.toNat; omega)) r1
        have r3 := cometWithExtendedAssetList_block_14422
          (immWords := wordsOf (immStore v)) (by omega) hret r2
        refine ⟨mem, Or.inl rfl, ?_⟩
        simp only [assetMembershipWriteResult, if_neg h24]
        exact ⟨σ, _, _, _, hs, r3⟩
  · by_cases h16 : offset.toNat < 16
    · have r1 := cometWithExtendedAssetList_block_14174_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
        (by rw [hright, ult_one h16]; decide) h
      dsimp only [cometWithExtendedAssetList_block_14174_fallthrough_stack] at r1
      rw [hright] at r1
      refine ⟨_, Or.inr rfl, ?_⟩
      rw [assetMembershipWrite_low evm account offset true h16]
      exact cometMembershipAssets (v := v) account true hstack hoffset h16 hret hs r1
    · have r1 := cometWithExtendedAssetList_block_14174_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 4 ≤ 1024; omega)
        (by rw [hright, ult_zero (show (UInt256.ofNat 16).toNat ≤ offset.toNat by change 16 ≤ offset.toNat; omega)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [cometWithExtendedAssetList_block_14174_taken_stack] at r1
      rw [hright] at r1
      by_cases h24 : offset.toNat < 24
      · have r2 := cometWithExtendedAssetList_block_14256_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
          (by rw [ult_one h24]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
        refine ⟨_, Or.inr rfl, ?_⟩
        rw [assetMembershipWrite_high evm account offset true h16 h24]
        exact cometMembershipReserved (v := v) account true hstack (by omega) h24
          hret hs r2
      · have r2 := cometWithExtendedAssetList_block_14256_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
          (ult_zero (show (UInt256.ofNat 24).toNat ≤ offset.toNat by
            change 24 ≤ offset.toNat; omega)) r1
        have r3 := cometWithExtendedAssetList_block_14267
          (immWords := wordsOf (immStore v)) (by omega) hret r2
        refine ⟨mem, Or.inl rfl, ?_⟩
        simp only [assetMembershipWriteResult, if_neg h24]
        exact ⟨σ, _, _, _, hs, r3⟩

end Benchmarks.CompoundIII.Comet
