import Benchmarks.CompoundIII.Comet.AbsorbReadModel
import Benchmarks.CompoundIII.Comet.SignedPresentValueEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_077

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hmem : 96 ≤ mem.size)
    (hb : free.toNat + 160 < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16996⟩
      (EVM.word account.val :: R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      UserBasicMemory (withdrawBaseReadMemory mem free evm account) free (absorbBasic evm account) ∧
      RD (deployedRuntime v) ee g s0 ⟨17021⟩
        ((absorbBasic evm account).principal :: EVM.word account.val :: free :: R)
        (withdrawBaseReadMemory mem free evm account) aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_16996 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 2 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_12490 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have hf : memLoad (UInt256.ofNat 64)
      (twoWordHashMem (EVM.word account.val) (UInt256.ofNat 5) mem) = free := by
    rw [twoWordHashMem_load_ge (mem := mem) (ptr := UInt256.ofNat 64)
      (EVM.word account.val) (UInt256.ofNat 5) (by decide) hmem]
    exact hfree
  obtain ⟨aw4, k4, C4, hm4, r4⟩ := cometAllocateUserBasic (v := v)
    (by change R.length + 1 + 9 ≤ 1024; omega) hf hb
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
  have hread : solcSlotWordAt (solcMappingSlot (UInt256.ofNat 5) (EVM.word account.val)) σ ee =
      (withdrawBaseBasic evm account).principal := by
    change solcSlotWordAt (userBasicSlot account) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot account)
    simpa only [hs.env] using (hs.storageRead (userBasicSlot account)).symm
  rw [hread] at hm4 r4
  change UserBasicMemory (withdrawBaseReadMemory mem free evm account) free
    (withdrawBaseBasic evm account) at hm4
  have r5 := cometWithExtendedAssetList_block_17009 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  dsimp only [cometWithExtendedAssetList_block_17009_stack] at r5
  change RD _ _ _ _ _ (UInt256.signextend _
    (memLoad free (withdrawBaseReadMemory mem free evm account)) :: _) _ _ _ _ _ _ at r5
  rw [hm4.principal, show (⟨12⟩ : UInt256) = UInt256.ofNat 12 from rfl,
    signextend104_idem] at r5
  exact ⟨_, _, _, hm4.normalized, r5⟩

theorem cometAbsorbPresent {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 15 ≤ 1024)
    (hbasic : UserBasicMemory mem ptr (absorbBasic evm account)) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17021⟩
      ((absorbBasic evm account).principal :: EVM.word account.val :: ptr :: R)
      mem aw rdata σ k C) :
    (-(2^103 : Int) < signed104 (absorbBasic evm account).principal ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17062⟩
        ((absorbBasic evm account).reserved :: (absorbBasic evm account).principal ::
          (absorbBasic evm account).assets :: EVM.word account.val :: absorbOldBalance evm account ::
          ptr :: R) mem aw' rdata σ k' C') ∨
    (¬ -(2^103 : Int) < signed104 (absorbBasic evm account).principal ∧
      RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_17021 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hp : UInt256.signextend (UInt256.ofNat 12) (absorbBasic evm account).principal =
      (absorbBasic evm account).principal := (withdrawBaseBasic evm account).normalized_principal
  dsimp only [cometWithExtendedAssetList_block_17021_stack] at r1
  have hrun := cometSignedPresentValue (v := v) (principal := (absorbBasic evm account).principal)
    (R := EVM.word account.val :: (absorbBasic evm account).principal :: ptr :: R)
    (ret := ⟨17031⟩)
    (by change R.length + 3 + 12 ≤ 1024; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) (by rw [hp]; exact r1)
  rcases hrun with ⟨hm, k2, C2, r2⟩ | ⟨hm, hrev⟩
  · have r3 := cometWithExtendedAssetList_block_17031 (immWords := wordsOf (immStore v))
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have ha : UInt256.land (UInt256.ofNat 65535) (absorbBasic evm account).assets =
        (absorbBasic evm account).assets := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (bits := 16) rfl (absorbBasic evm account).assets_lt
    dsimp only [cometWithExtendedAssetList_block_17031_stack] at r3
    have hassets : memLoad (ptr + UInt256.ofNat 96) mem = (absorbBasic evm account).assets :=
      hbasic.assets
    rw [hassets, ha] at r3
    have r4 := cometWithExtendedAssetList_block_17047 (immWords := wordsOf (immStore v))
      (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    have hr : UInt256.land (UInt256.ofNat 255) (absorbBasic evm account).reserved =
        (absorbBasic evm account).reserved := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (bits := 8) rfl (absorbBasic evm account).reserved_lt
    dsimp only [cometWithExtendedAssetList_block_17047_stack] at r4
    have hreserved : memLoad (ptr + UInt256.ofNat 128) mem =
        (absorbBasic evm account).reserved := hbasic.reserved
    rw [hreserved, hr] at r4
    exact Or.inl ⟨hm, _, _, _, r4⟩
  · exact Or.inr ⟨hm, hrev⟩

end Benchmarks.CompoundIII.Comet
