import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsModel
import Benchmarks.CompoundIII.Comet.TotalsPrincipalRead
import Benchmarks.CompoundIII.Comet.Checked104Evm
import Benchmarks.CompoundIII.Comet.TotalsPrincipalStoreEvm
import Benchmarks.CompoundIII.Comet.TotalsPrincipalStatic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_058
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometSupplyBaseTotals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw supplied repaid ptr principal amount sender dst : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024) (hS : supplied.toNat < 2^104) (hB : repaid.toNat < 2^104)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨12543⟩
      (supplied :: repaid :: UInt256.ofNat 12598 :: ptr :: principal :: UInt256.ofNat 12604 ::
        amount :: sender :: UInt256.ofNat 12591 :: dst :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ⟨12598⟩
      (ptr :: principal :: UInt256.ofNat 12604 :: amount :: sender :: supplied :: dst :: R) (supplyBaseTotalsOutcome evm supplied repaid) := by
  have hword := sourceState_supplyPrincipalRead hs
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_12543
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 15 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7787
    (immWords := wordsOf (immStore v)) (by change R.length + 13 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _ (UInt256.land _ (solcSlotWordAt (UInt256.ofNat 1) σ ee) ::
    supplied :: UInt256.ofNat 12568 :: UInt256.ofNat 12575 :: repaid :: UInt256.ofNat 12591 ::
    UInt256.ofNat 12598 :: ptr :: principal :: UInt256.ofNat 12604 :: amount :: sender ::
    supplied :: dst :: R) _ _ _ _ _ _ at r2
  rw [hword] at r2
  have r3 := cometWithExtendedAssetList_block_12563
    (immWords := wordsOf (immStore v)) (by change R.length + 14 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  rcases cometCheckedAdd104 (v := v) (x := withdrawBaseTotal evm false) (y := supplied)
      (by change R.length + 11 + 6 ≤ 1024; omega)
      (totalsPrincipalWord_lt _ false) hS
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
    ⟨hle, k4, C4, r4⟩ | ⟨hle, hr⟩
  · have r5 := cometWithExtendedAssetList_block_12568
      (immWords := wordsOf (immStore v)) (by change R.length + 12 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    cases hp : evm.executionEnv.perm
    · simp only [supplyBaseTotalsOutcome, if_pos hle, hp, Bool.false_eq_true, if_false, internalRun]
      exact cometStoreSupplyPrincipalStatic (v := v)
        (by change R.length + 10 + 7 ≤ 1024; omega) (by rw [← hs.env]; exact hp) r5
    · have hrS := cometStoreTotalsPrincipal (v := v) false
        (by change R.length + 10 + 7 ≤ 1024; omega) hp hs
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
      obtain ⟨σ1, k6, C6, hs1, r6⟩ := hrS
      change SourceState s0 ee σ1 (supplyBaseSupplyState evm supplied) at hs1
      have hwordB := sourceState_borrowPrincipalRead hs1
      obtain ⟨k7, C7, r7⟩ := cometWithExtendedAssetList_block_12575
        (immWords := wordsOf (immStore v)) (by change R.length + 10 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      have r8 := cometWithExtendedAssetList_block_7871
        (immWords := wordsOf (immStore v)) (by change R.length + 10 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
      change RD _ _ _ _ _ (UInt256.land _ (UInt256.shiftRight
        (solcSlotWordAt (UInt256.ofNat 1) σ1 ee) (UInt256.ofNat 104)) :: repaid ::
        UInt256.ofNat 12591 :: UInt256.ofNat 12598 :: ptr :: principal :: UInt256.ofNat 12604 ::
        amount :: sender :: supplied :: dst :: R) _ _ _ _ _ _ at r8
      rw [hwordB] at r8
      have r9 := cometWithExtendedAssetList_block_12586
        (immWords := wordsOf (immStore v)) (by change R.length + 11 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
      rcases cometCheckedSub104 (v := v)
          (x := withdrawBaseTotal (supplyBaseSupplyState evm supplied) true) (y := repaid)
          (by change R.length + 8 + 6 ≤ 1024; omega)
          (totalsPrincipalWord_lt _ true) hB
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9 with
        ⟨hadd, k10, C10, r10⟩ | ⟨hadd, hr⟩
      · have r11 := cometWithExtendedAssetList_block_12591
          (immWords := wordsOf (immStore v)) (by change R.length + 9 + 2 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r10
        have hp1 : (supplyBaseSupplyState evm supplied).executionEnv.perm = true := by
          simpa only [supplyBaseSupplyState, storeTotalsPrincipal, storageStore_executionEnv]
            using hp
        have hrB := cometStoreTotalsPrincipal (v := v) true
          (by change R.length + 7 + 7 ≤ 1024; omega) hp1 hs1
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r11
        simpa only [supplyBaseTotalsOutcome, if_pos hle, hp, if_true, if_pos hadd,
          supplyBaseTotalsState] using hrB
      · simpa only [supplyBaseTotalsOutcome, if_pos hle, hp, if_true, if_neg hadd, internalRun]
          using hr
  · simpa only [supplyBaseTotalsOutcome, if_neg hle, internalRun] using hr

end Benchmarks.CompoundIII.Comet
