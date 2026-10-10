import Benchmarks.CompoundIII.Comet.WithdrawCollateralTransferEvm
import Benchmarks.CompoundIII.Comet.CollateralCheckEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_070

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def withdrawCollateralCheckStack (src recipient asset : AccountAddress)
    (amount ret : UInt256) (R : List UInt256) : List UInt256 :=
  EVM.word src.val :: withdrawCollateralTransferStack src recipient asset amount ret R

theorem cometWithdrawCollateralCheck {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size) (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16441⟩
      (withdrawCollateralCheckStack src recipient asset amount ret R) mem aw rdata σ k C) :
    ∃ result, WithdrawCollateralCheck v src recipient asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have r1 := cometWithExtendedAssetList_block_16441
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨result, ht, hr⟩ := cometCollateralCheck (v := v) true src
    (by change R.length + 8 + 35 ≤ 1024; omega) hfree hlo hmem hgap hbound
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .failed ht, hr⟩
  | some pair =>
    obtain ⟨evm', value⟩ := pair
    obtain ⟨σ', mem', free', aw', data, k', C', hs', hm', hf', hlo', hb', _, r2⟩ := hr
    cases value
    · have r3 := cometWithExtendedAssetList_block_16450_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 8 + 2 ≤ 1024; omega)
        (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      exact ⟨.reverted, .rejected ht,
        cometWithExtendedAssetList_block_15192 (immWords := wordsOf (immStore v))
          (by change R.length + 8 + 3 ≤ 1024; omega) r3⟩
    · have r3 := cometWithExtendedAssetList_block_16450_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 8 + 2 ≤ 1024; omega)
        (by decide) r2
      obtain ⟨result, htransfer, hr⟩ := cometWithdrawCollateralTransfer (v := v)
        src recipient asset (by omega) hamount hf' hlo' (by omega) hret hs' r3
      exact ⟨result, .accepted ht htransfer, hr⟩

end Benchmarks.CompoundIII.Comet
