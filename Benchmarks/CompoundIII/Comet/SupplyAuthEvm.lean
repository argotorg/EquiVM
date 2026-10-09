import Benchmarks.CompoundIII.Comet.AuthorizationSource
import Benchmarks.CompoundIII.Comet.PermissionState
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_056
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_035
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometSupplyAuth {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw amount : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (operator sender dst asset : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12067⟩
      (EVM.word operator.val :: EVM.word sender.val :: EVM.word dst.val ::
        EVM.word asset.val :: amount :: R) mem aw rdata σ k C) :
    if AuthorizationValid evm ⟨0, by decide⟩ operator sender then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨12105⟩
        (EVM.word asset.val :: EVM.word dst.val :: amount :: EVM.word sender.val :: R)
        (permissionMemory (EVM.word sender.val) (EVM.word operator.val) mem) aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hp : pauseBitWord evm ⟨0, by decide⟩ =
      UInt256.land (UInt256.shiftRight (solcSlotWordAt ⟨1⟩ σ ee) ⟨248⟩) ⟨1⟩ := by
    rw [pauseBitWord, pauseFlagsWord_eq_shift, hs.storageRead]
    rfl
  by_cases hz : (pauseBitWord evm ⟨0, by decide⟩).toNat = 0
  · have hw := uint256_toNat_eq_zero hz
    rw [hp] at hw
    obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_12067_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) hw h
    have r2 := cometWithExtendedAssetList_block_12084
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨_, _, _, r3⟩ := cometHasPermission (v := v)
      (by change R.length + 5 + 8 ≤ 1024; omega)
      (addressWord_val_canonical sender) (addressWord_val_canonical operator)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_12096
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    by_cases ha : permissionBool evm sender operator = true
    · have hn : permissionRuntimeWord σ ee (EVM.word sender.val) (EVM.word operator.val) ≠ ⟨0⟩ :=
        permissionRuntime_nonzero hs ha
      rw [if_pos ⟨hz, ha⟩]
      exact ⟨_, _, _, cometWithExtendedAssetList_block_12100_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
        (isZero_eq_zero_of_ne hn) r4⟩
    · have hw : permissionRuntimeWord σ ee (EVM.word sender.val) (EVM.word operator.val) = ⟨0⟩ :=
        permissionRuntime_zero hs ha
      have r5 := cometWithExtendedAssetList_block_12100_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
        (by change UInt256.isZero _ ≠ ⟨0⟩; rw [hw]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      rw [if_neg (fun hh ↦ ha hh.2)]
      exact cometWithExtendedAssetList_block_3682 (immWords := wordsOf (immStore v))
        (by change R.length + 4 + 3 ≤ 1024; omega) r5
  · obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_12067_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by intro he; apply hz; exact congrArg UInt256.toNat (hp.trans he))
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    rw [if_neg (fun hh ↦ hz hh.1)]
    exact cometWithExtendedAssetList_block_6727 (immWords := wordsOf (immStore v))
      (by change R.length + 5 + 3 ≤ 1024; omega) r1

end Benchmarks.CompoundIII.Comet
