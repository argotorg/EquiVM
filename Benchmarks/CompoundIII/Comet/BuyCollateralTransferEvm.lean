import Benchmarks.CompoundIII.Comet.BuyCollateralModel
import Benchmarks.CompoundIII.Comet.TransferOutInternal
import Benchmarks.CompoundIII.Comet.Safe128Evm
import Benchmarks.CompoundIII.Comet.Mask128Evm
import Benchmarks.CompoundIII.Comet.ReentrancyEvm
import Benchmarks.CompoundIII.Comet.ReturnOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_001
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_034
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometBuyCollateralFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6622⟩ (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)
      mem aw rdata σ k C) :
    returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty (.ok (reentrancyState evm false)) := by
  obtain ⟨k', C', hr⟩ := cometWithExtendedAssetList_block_6622 (immWords := wordsOf (immStore v))
    hstack hperm (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hcopy : memLoad (UInt256.ofNat 0)
      ((immutableLayout.runtime cometWithExtendedAssetListBytecode (wordsOf (immStore v))).write
        (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) =
      reentrancySlot := reentrancyCopyMemory_word v mem
  rw [hcopy] at hr
  have hr := cometWithExtendedAssetList_block_22 (immWords := wordsOf (immStore v))
    (by change R.length + 0 ≤ 1024; omega) hr
  have hs' := sourceState_reentrancy hs false
  change RDret (deployedRuntime v) g s0
    (sstoreAccountMap ee.codeOwner σ reentrancySlot (reentrancyValue false)) ByteArray.empty at hr
  simpa only [returnOutcomeRun, hs'.accounts] using hr

theorem cometBuyCollateralTransfer {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free base amount : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 24 ≤ 1024) (hperm : ee.perm = true)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hb : free.toNat + 68 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6523⟩
      (EVM.word recipient.val :: EVM.word asset.val :: base :: amount :: R) mem aw rdata σ k C) :
    ∃ result, BuyCollateralTransfer asset recipient amount evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  have r1 := cometWithExtendedAssetList_block_6523 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_6523_stack] at r1
  rcases cometSafe128 (v := v) (by change R.length + 8 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hw, k1, C1, r1⟩ | ⟨hw, hr⟩
  · have r2 := cometWithExtendedAssetList_block_6575 (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have r3 := cometMask128 (v := v) (by change R.length + 7 + 5 ≤ 1024; omega) hw
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_6580 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    simp only [cometWithExtendedAssetList_block_6580_stack] at r4
    obtain ⟨result, ht, hr⟩ := cometTransferOutInternal (v := v)
      (by change R.length + 5 + 17 ≤ 1024; omega) hfree hlo hb
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r4
    cases result with
    | none => exact ⟨.reverted, .failed hw ht, hr⟩
    | some evm' =>
      obtain ⟨σ', mem', aw', out, k', C', hs', _, _, hr⟩ := hr
      have r5 := cometWithExtendedAssetList_block_6587 (immWords := wordsOf (immStore v))
        (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) hr
      simp only [cometWithExtendedAssetList_block_6587_stack] at r5
      exact ⟨_, .done hw ht (by rw [hs'.env]; exact hperm),
        cometBuyCollateralFinish (v := v) (by omega) hperm hs' r5⟩
  · exact ⟨.reverted, .tooLarge hw, hr⟩

end Benchmarks.CompoundIII.Comet
