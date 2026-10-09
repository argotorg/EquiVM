import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.BuyCollateralInternal
import Benchmarks.CompoundIII.Comet.BuyCollateralCalldata
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometDecodeBuyCollateral {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hsz : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨6359⟩ R mem aw rdata σ k C) :
    if BuyCollateralCalldataValid ee then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨6395⟩
        (calldataWord ee.calldata 4 :: calldataWord ee.calldata 100 :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hlo : 132 ≤ ee.calldata.size
  · by_cases hhi : ee.calldata.size < 2^255 + 4
    · have r1 := cometWithExtendedAssetList_block_6359_fallthrough
        (immWords := wordsOf (immStore v)) (by omega)
        (calldataLength_ok (by decide) hlo hhi hsize) h
      have r2 := cometWithExtendedAssetList_block_6371 (immWords := wordsOf (immStore v))
        (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      change RD _ _ _ _ _ (calldataWord ee.calldata 4 :: UInt256.ofNat 6382 ::
        calldataWord ee.calldata 4 :: R) _ _ _ _ _ _ at r2
      by_cases ha : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
      · obtain ⟨k3, C3, r3⟩ := cometValidateAddress_ok (v := v)
          (by change R.length + 1 + 5 ≤ 1024; omega) ha
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
        have r4 := cometWithExtendedAssetList_block_6382 (immWords := wordsOf (immStore v))
          (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        change RD _ _ _ _ _ (calldataWord ee.calldata 100 :: UInt256.ofNat 6395 ::
          calldataWord ee.calldata 4 :: calldataWord ee.calldata 100 :: R) _ _ _ _ _ _ at r4
        by_cases hr : (calldataWord ee.calldata 100).toNat < EVM.addressModulus
        · rw [if_pos ⟨hlo, hhi, ha, hr⟩]
          exact cometValidateAddress_ok (v := v) (by change R.length + 2 + 5 ≤ 1024; omega) hr
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
        · rw [if_neg (fun hh ↦ hr hh.2.2.2)]
          exact cometValidateAddress_bad (v := v) (by change R.length + 3 + 4 ≤ 1024; omega) hr r4
      · rw [if_neg (fun hh ↦ ha hh.2.2.1)]
        exact cometValidateAddress_bad (v := v) (by change R.length + 2 + 4 ≤ 1024; omega) ha r2
    · rw [if_neg (fun hh ↦ hhi hh.2.1)]
      have r1 := cometWithExtendedAssetList_block_6359_taken (immWords := wordsOf (immStore v))
        (by omega) (calldataLength_huge (by decide) (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact cometRevert1410 (by omega) r1
  · rw [if_neg (fun hh ↦ hlo hh.1)]
    have r1 := cometWithExtendedAssetList_block_6359_taken (immWords := wordsOf (immStore v))
      (by omega) (calldataLength_short (by decide) hsz (by omega) hsize)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometRevert1410 (by omega) r1

def BuyCollateralResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ BuyCollateralCalldataValid I then
    ∃ result, BuyCollateralTrace v
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (AccountAddress.ofNat (calldataWord I.calldata 100).toNat)
      (calldataWord I.calldata 36) (calldataWord I.calldata 68) s0 result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result
  else RDrev (deployedRuntime v) g s0

theorem buyCollateralX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 64)) :
    BuyCollateralResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachBuyCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_808 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_6352_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have hd := cometDecodeBuyCollateral (v := v) (by decide) hsz hsize rd2
    by_cases hargs : BuyCollateralCalldataValid I
    · rw [if_pos hargs] at hd
      obtain ⟨k3, C3, rd3⟩ := hd
      rw [← addressWord_eq_ofNat_address hargs.2.2.1,
        ← addressWord_eq_ofNat_address hargs.2.2.2] at rd3
      unfold BuyCollateralResult
      rw [if_pos ⟨hv, hargs⟩]
      exact cometBuyCollateralCall (v := v) (by decide) rfl rfl SourceState.init rd3
    · rw [if_neg hargs] at hd
      simpa only [BuyCollateralResult, hargs, and_false, if_false] using hd
  · simp only [BuyCollateralResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_6352_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
