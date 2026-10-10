import Benchmarks.CompoundIII.Comet.AccrueAccountModel
import Benchmarks.CompoundIII.Comet.UpdateBaseEvm
import Benchmarks.CompoundIII.Comet.UserBasicLoadEvm
import Benchmarks.CompoundIII.Comet.MemoryAllocate
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: terminal EVM outcomes corresponding to a void source function.
def voidOutcomeRun (code : ByteArray) (g : Sat256) (s0 : EVM.State)
    (result : InternalOutcome) : Prop :=
  match result with
  | .ok evm' => RDret code g s0 evm'.accountMap ByteArray.empty
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

theorem cometAccrueAccountUpdate {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} (addr : AccountAddress)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨5313⟩ [EVM.word addr.val, ⟨22⟩]
      solcFreePtrMem aw rdata σ k C) :
    voidOutcomeRun (deployedRuntime v) g s0 (accrueAccountUpdate v evm addr) := by
  let mem := twoWordHashMem (EVM.word addr.val) ⟨5⟩ solcFreePtrMem
  have hclean : UInt256.land (EVM.word addr.val)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = EVM.word addr.val :=
    solcAddrMask_clean (word_val_addr_canonical addr)
  have hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 := by
    apply loadedWord_of_read
    · rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size]; decide
    · exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have hslot : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem = userBasicSlot addr :=
    twoWordHashMem_solcMappingSlot_any ⟨5⟩ (EVM.word addr.val) solcFreePtrMem
  have r1 := cometWithExtendedAssetList_block_5313 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_5313_stack,
    cometWithExtendedAssetList_block_5313_memory] at r1
  rw [hclean] at r1
  change RD _ _ _ _ _
    (memLoad (UInt256.ofNat 64) mem :: UInt256.ofNat 160 :: UInt256.ofNat 5353 ::
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) mem :: UInt256.ofNat 5416 ::
      memLoad (UInt256.ofNat 64) mem :: EVM.word addr.val :: [⟨22⟩]) mem _ _ _ _ _ at r1
  rw [hfree, hslot] at r1
  obtain ⟨aw2, k2, C2, r2⟩ := cometAllocate160 (v := v)
    (by change 11 ≤ 1024; decide) (by decide) (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨aw3, k3, C3, hm3, r3⟩ := cometLoadUserBasic (v := v)
    (by change 9 ≤ 1024; decide) (by decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  have hread : solcSlotWordAt (userBasicSlot addr) σ ee =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (userBasicSlot addr) := by
    simpa only [hs.env] using (hs.storageRead (userBasicSlot addr)).symm
  rw [hread] at hm3 r3
  have r4 := cometWithExtendedAssetList_block_5416 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  dsimp only [cometWithExtendedAssetList_block_5416_stack] at r4
  have hp : memLoad (UInt256.ofNat 128) _ = UInt256.signextend (UInt256.ofNat 12)
      (accrueAccountBasic evm addr).principal := hm3.principal
  rw [hp, signextend104_idem] at r4
  have hr := cometUpdateBasePrincipal (v := v) addr (by decide) hm3 (by decide) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
  change internalMemoryRun _ _ _ _ _ _ _ _ (accrueAccountUpdate v evm addr) at hr
  cases hx : accrueAccountUpdate v evm addr with
  | ok evm' =>
      rw [hx] at hr
      obtain ⟨σ', aw', k', C', hs', hr⟩ := hr
      simp only [voidOutcomeRun]
      rw [← hs'.accounts]
      exact cometWithExtendedAssetList_block_22 (immWords := wordsOf (immStore v))
        (by decide) hr
  | reverted => simpa only [hx, internalMemoryRun, voidOutcomeRun] using hr
  | staticViolation => simpa only [hx, internalMemoryRun, voidOutcomeRun] using hr

end Benchmarks.CompoundIII.Comet
