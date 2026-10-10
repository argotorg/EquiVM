import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.TransferInternalEvm
import Benchmarks.CompoundIII.Comet.TwoAddressUintDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_011
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferFromCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw amount : UInt256} {σ : AccountMap} {k C : Nat} (src dst : AccountAddress)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨2066⟩
      [amount, EVM.word dst.val, EVM.word src.val, ⟨2116⟩]
      solcFreePtrMem aw rdata σ k C) :
    ∃ result, TransferInternalTrace v ee.source src dst v.baseToken amount evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData true) result := by
  have r1 := cometWithExtendedAssetList_block_2066 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  apply cometTransferInternalStart (v := v) true ee.source src dst v.baseToken
    (by change 10 ≤ 1024; decide) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) ?_ r1
  intro evm' σ' aw' k' C' hs' hp r2
  have r3 := cometWithExtendedAssetList_block_2076 (immWords := wordsOf (immStore v))
    (by change 7 ≤ 1024; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_2076_stack] at r3
  rw [wordsOf_immStore_baseToken] at r3
  apply cometTransferInternalAfter (v := v) true ee.source src dst v.baseToken
    (free := ⟨128⟩) (by decide) hp ?_ (by decide) ?_ ?_ hs' r3
  · exact (reentrancyMemory_free v _ (by rw [solcFreePtrMem_size])).trans solcFreePtrMem_mload64
  · rw [reentrancyMemory_size v _ (by rw [solcFreePtrMem_size]; decide), solcFreePtrMem_size]
  · have := v.numAssets_lt
    change 128 + 736 + 1696 * v.numAssets.toNat < 2^64
    omega

def TransferFromResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ TwoAddressUintCalldataValid I then
    ∃ result, TransferInternalTrace v I.source
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (AccountAddress.ofNat (calldataWord I.calldata 36).toNat) v.baseToken
      (calldataWord I.calldata 68) s0 result ∧ returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData true) result
  else RDrev (deployedRuntime v) g s0

theorem transferFromX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 8)) :
    TransferFromResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachTransferFromBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1312 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_2046_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have rd3 := cometWithExtendedAssetList_block_2053
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hd := cometDecodeTwoAddressesUint (v := v) (by decide) hsz hsize
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
    by_cases hargs : TwoAddressUintCalldataValid I
    · rw [if_pos hargs] at hd
      obtain ⟨k4, C4, rd4⟩ := hd
      rw [← addressWord_eq_ofNat_address hargs.2.2.1,
        ← addressWord_eq_ofNat_address hargs.2.2.2] at rd4
      unfold TransferFromResult
      rw [if_pos ⟨hv, hargs⟩]
      exact cometTransferFromCall _ _ SourceState.init rd4
    · rw [if_neg hargs] at hd
      simpa only [TransferFromResult, hargs, and_false, if_false] using hd
  · simp only [TransferFromResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_2046_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
