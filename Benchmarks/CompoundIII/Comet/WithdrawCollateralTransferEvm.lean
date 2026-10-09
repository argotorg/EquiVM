import Benchmarks.CompoundIII.Comet.CollateralEventEvm
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome
import Benchmarks.CompoundIII.Comet.TransferOutInternal
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_075
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawCollateralTransferStack (src recipient asset : AccountAddress)
    (amount ret : UInt256) (R : List UInt256) : List UInt256 :=
  [⟨2^128-1⟩, EVM.word recipient.val, solcAddrMask, EVM.word asset.val,
    EVM.word src.val, amount, EVM.word asset.val, ret] ++ R

theorem cometWithdrawCollateralTransfer {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 24 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hbound : free.toNat + 68 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16456⟩
      (withdrawCollateralTransferStack src recipient asset amount ret R) mem aw rdata σ k C) :
    ∃ result, WithdrawCollateralTransfer asset recipient amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_16456
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_16456_stack] at r1
  rw [u256LandMaskCleanOfToNat amount ⟨2^128-1⟩ (bits := 128) rfl hamount] at r1
  obtain ⟨result, ht, hr⟩ := cometTransferOutInternal (v := v)
    (by change R.length + 7 + 17 ≤ 1024; omega) hfree hlo hbound
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some evm' =>
    obtain ⟨σ', mem', aw', out, k', C', hs', hf', _, r2⟩ := hr
    have r3 := cometWithExtendedAssetList_block_16502
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 9 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    have r4 := cometWithExtendedAssetList_block_13801
      (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    exact ⟨emitOutcome evm', .done ht,
      (cometCollateralLog (v := v) (by change R.length + 8 ≤ 1024; omega) hret hs' r4).dynamic⟩

end Benchmarks.CompoundIII.Comet
