import Benchmarks.CompoundIII.Comet.TransferCollateralPrefixEvm
import Benchmarks.CompoundIII.Comet.TransferCollateralTailEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferCollateral {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src dst asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (ha : amount.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 672 + 1696 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15329⟩
      (EVM.word src.val :: EVM.word dst.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, TransferCollateralTrace v src dst asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have hp := cometTransferCollateralPrefix src dst asset (by omega) ha hs h
  cases he : transferCollateralPrefixOutcome evm src dst asset amount with
  | reverted => rw [he] at hp; exact ⟨.reverted, .reverted he, hp⟩
  | staticViolation => rw [he] at hp; exact ⟨.staticViolation, .staticViolation he, hp⟩
  | ok evm' =>
    rw [he] at hp
    obtain ⟨σ', aw', k', C', hs', r1⟩ := hp
    have hsub : amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat := by
      by_contra hn
      simp only [transferCollateralPrefixOutcome, if_neg hn] at he
      cases he
    have hadd : (withdrawCollateralBalance evm dst asset).toNat + amount.toNat < 2^128 := by
      by_contra hn
      simp only [transferCollateralPrefixOutcome, if_pos hsub, if_neg hn] at he
      cases he
    have hsrc : (transferCollateralSrcNext evm src asset amount).toNat < 2^128 := by
      rw [transferCollateralSrcNext, usub_toNat hsub]
      have hb : (withdrawCollateralBalance evm src asset).toNat < 2^128 := low128_lt _
      omega
    have hdst : (transferCollateralDstNext evm dst asset amount).toNat < 2^128 := by
      rw [transferCollateralDstNext, uadd_toNat,
        Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
      exact hadd
    obtain ⟨result, ht, hr⟩ := cometTransferCollateralTail src dst asset hstack
      (low128_lt _) hsrc (low128_lt _) hdst
      (transferCollateralPrefixMemory_free src dst asset hmem hfree) hlo hbound hret hs' r1
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
