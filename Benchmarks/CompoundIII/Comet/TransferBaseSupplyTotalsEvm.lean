import Benchmarks.CompoundIII.Comet.TransferBaseTotalsModel
import Benchmarks.CompoundIII.Comet.TotalsPrincipalRead
import Benchmarks.CompoundIII.Comet.Checked104Evm
import Benchmarks.CompoundIII.Comet.TotalsPrincipalStoreEvm
import Benchmarks.CompoundIII.Comet.TotalsPrincipalStatic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_068
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_069

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferBaseSupplyTotals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw supplied repaid withdrawn borrowed srcNext srcPtr dstNext dstPtr balance src : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hS : supplied.toNat < 2^104) (hW : withdrawn.toNat < 2^104)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14841⟩
      (supplied :: repaid :: srcNext :: srcPtr :: dstNext :: dstPtr :: balance :: withdrawn ::
        src :: borrowed :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ⟨14887⟩
      (borrowed :: repaid :: srcNext :: srcPtr :: dstNext :: dstPtr :: balance :: withdrawn ::
        src :: supplied :: R) (totalsChangeOutcome evm false supplied withdrawn) := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14841
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7787
    (immWords := wordsOf (immStore v)) (by change R.length + 12 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _ (UInt256.land _ (solcSlotWordAt (UInt256.ofNat 1) σ ee) :: supplied ::
    withdrawn :: borrowed :: repaid :: srcNext :: srcPtr :: dstNext :: dstPtr :: balance ::
    withdrawn :: src :: supplied :: R) _ _ _ _ _ _ at r2
  rw [sourceState_supplyPrincipalRead hs] at r2
  have r3 := cometWithExtendedAssetList_block_14856
    (immWords := wordsOf (immStore v)) (by change R.length + 11 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  rcases cometCheckedAdd104 (v := v) (x := withdrawBaseTotal evm false) (y := supplied)
      (by change R.length + 11 + 6 ≤ 1024; omega)
      (totalsPrincipalWord_lt _ false) hS
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
    ⟨ha, k4, C4, r4⟩ | ⟨ha, hr⟩
  · have hsum : (withdrawBaseTotal evm false + supplied).toNat < 2^104 := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (show _ < UInt256.size by change _ < 2^256; omega)]
      exact ha
    have r5 := cometWithExtendedAssetList_block_14866
      (immWords := wordsOf (immStore v)) (by change R.length + 10 + 4 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    rcases cometCheckedSub104 (v := v) (by change R.length + 10 + 6 ≤ 1024; omega) hsum hW
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5 with
      ⟨hd, k6, C6, r6⟩ | ⟨hd, hr⟩
    · have r7 := cometWithExtendedAssetList_block_14876
        (immWords := wordsOf (immStore v)) (by change R.length + 10 + 4 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      have hf : TotalsChangeFits evm false supplied withdrawn := ⟨ha, hd⟩
      cases hp : evm.executionEnv.perm
      · simp only [totalsChangeOutcome, if_pos hf, hp, Bool.false_eq_true, if_false, internalRun]
        exact cometStoreSupplyPrincipalStatic (v := v)
          (by change R.length + 10 + 7 ≤ 1024; omega) (by rw [← hs.env]; exact hp) r7
      · have hw := cometStoreTotalsPrincipal (v := v) false
          (by change R.length + 10 + 7 ≤ 1024; omega) hp hs
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
        simpa only [totalsChangeOutcome, if_pos hf, hp, if_true, totalsChangeState] using hw
    · simp only [totalsChangeOutcome,
        if_neg (fun hf : TotalsChangeFits evm false supplied withdrawn ↦ hd hf.2), internalRun]
      exact hr
  · simp only [totalsChangeOutcome,
      if_neg (fun hf : TotalsChangeFits evm false supplied withdrawn ↦ ha hf.1), internalRun]
    exact hr

end Benchmarks.CompoundIII.Comet
