import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeSimulation

/-! Complete accrued-fee helper simulation, including external calls and allocation failures. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem accruedAssetsTailStorage {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap} {real ptr : UInt256}
    (hl : AccruedAssetsTailLocals v frame real ptr) (hs : SourceState s0 I σ evm) :
    let last := codeOwnerStorageWord I σ ⟨22⟩
    let lost := codeOwnerStorageWord I σ ⟨23⟩
    evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value last) ∧
    evalExpr? config frame evm (.storage ⟨"lostAssets", []⟩) = .ok (uint256Value lost) ∧
    evalExpr? config (accruedTotalFrame frame last lost real) evm
      (.storage ⟨"lastTotalAssets", []⟩) = .ok (uint256Value last) := by
  dsimp only
  have hc := hl.contract
  have hla := hl.lastAssets
  have hlo := hl.lostAssets
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hla hlo
  subst c
  refine ⟨?_, ?_, ?_⟩
  · rw [evalStorage_lastTotalAssets evm locals imms hla, hs.storageRead]
  · rw [evalStorage_lostAssets evm locals imms hlo, hs.storageRead]
  · have hn : (accruedTotalFrame
        { contract := contract, locals := locals, immutables := imms }
        (codeOwnerStorageWord I σ ⟨22⟩) (codeOwnerStorageWord I σ ⟨23⟩) real).locals.get?
        "lastTotalAssets" = none := by
      dsimp only [accruedTotalFrame, accruedLossFrame]
      rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
      exact hla
    exact (evalStorage_lastTotalAssets evm _ imms hn).trans (by rw [hs.storageRead])

theorem accruedAssetsSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 35 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12247⟩ (ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (lost total shares ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
        allocatedAccruedFeeAssetsFunction.body
        (.returned frame' evm'
          [.tuple [uint256Value shares, uint256Value total, uint256Value lost],
            uint256Value ptr']) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        ([lost, total, shares] ++ R) mem' aw' out evm'.accountMap k' C' := by
  rcases accruedAssetsPrefixSimulation v hstack hcalldata hfree hlo hmem hs rd with
    hbad | ⟨evm', frame', real, ptr', mem', out, hs', hstore, hl,
      hfree', hlo', hmem', hprefix, aw1, k1, C1, h1⟩
  · exact .inl hbad
  · obtain ⟨ha, hb, ha'⟩ := accruedAssetsTailStorage hl hs'
    by_cases ht : accruedTotalsFit (codeOwnerStorageWord I evm'.accountMap ⟨22⟩)
        (codeOwnerStorageWord I evm'.accountMap ⟨23⟩) real
    · have hsrc := accruedTotalsSource ha hb ha' hl.total hl.newLost hl.newTotal ht
      obtain ⟨aw2, k2, C2, h2⟩ := accruedTotalsReturn v (by omega) ht h1
      rcases accruedFeeSimulation v (by omega)
          (accruedFeeLocals_afterTotals _ _ hl) hs' hret h2 with
        ⟨hbad, hrev⟩ | ⟨frame'', shares, hdone, hret'⟩
      · exact .inl ⟨ExecFuncBody.execBlockRevert (hprefix _ (hsrc.run hbad)), hrev⟩
      · exact .inr ⟨evm', frame'', _, _, shares, ptr', mem', out,
          hs', hstore, hfree', hlo', hmem',
          ExecFuncBody.execBlockRet (hprefix _ (hsrc.run hdone)), hret'⟩
    · exact .inl
        ⟨ExecFuncBody.execBlockRevert (hprefix _
          (accruedTotalsReverts ha hb hl.total hl.newLost ht)),
          accruedTotalsRevert v (by omega) ht h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
