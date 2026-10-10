import Benchmarks.CompoundIII.Comet.TransferBaseTotalsModel
import Benchmarks.CompoundIII.Comet.TotalsPrincipalRead
import Benchmarks.CompoundIII.Comet.Checked104Evm
import Benchmarks.CompoundIII.Comet.TotalsPrincipalStoreEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_069

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferBaseBorrowTotals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw borrowed repaid : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hB : borrowed.toNat < 2^104) (hR : repaid.toNat < 2^104)
    (hp : evm.executionEnv.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14887⟩ (borrowed :: repaid :: R)
      mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ⟨14930⟩ R
      (totalsChangeOutcome evm true borrowed repaid) := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14887
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_7871
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  change RD _ _ _ _ _ (UInt256.land _ (UInt256.shiftRight
    (solcSlotWordAt (UInt256.ofNat 1) σ ee) (UInt256.ofNat 104)) :: borrowed :: repaid :: R)
    _ _ _ _ _ _ at r2
  rw [sourceState_borrowPrincipalRead hs] at r2
  have r3 := cometWithExtendedAssetList_block_14899
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  rcases cometCheckedAdd104 (v := v) (x := withdrawBaseTotal evm true) (y := borrowed)
      (by change R.length + 1 + 6 ≤ 1024; omega)
      (totalsPrincipalWord_lt _ true) hB
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
    ⟨ha, k4, C4, r4⟩ | ⟨ha, hr⟩
  · have hsum : (withdrawBaseTotal evm true + borrowed).toNat < 2^104 := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (show _ < UInt256.size by change _ < 2^256; omega)]
      exact ha
    have r5 := cometWithExtendedAssetList_block_14909
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    rcases cometCheckedSub104 (v := v) (by omega) hsum hR
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5 with
      ⟨hd, k6, C6, r6⟩ | ⟨hd, hr⟩
    · have r7 := cometWithExtendedAssetList_block_14919
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      have hw := cometStoreTotalsPrincipal (v := v) true hstack hp hs
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
      simpa only [totalsChangeOutcome, if_pos (show TotalsChangeFits evm true borrowed repaid
        from ⟨ha, hd⟩), hp, if_true, totalsChangeState] using hw
    · simp only [totalsChangeOutcome,
        if_neg (fun hf : TotalsChangeFits evm true borrowed repaid ↦ hd hf.2), internalRun]
      exact hr
  · simp only [totalsChangeOutcome,
      if_neg (fun hf : TotalsChangeFits evm true borrowed repaid ↦ ha hf.1), internalRun]
    exact hr

end Benchmarks.CompoundIII.Comet
