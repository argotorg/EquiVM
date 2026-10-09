import Benchmarks.CompoundIII.Comet.WithdrawCollateralPrefixEvm
import Benchmarks.CompoundIII.Comet.WithdrawCollateralTailEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawCollateral {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (src recipient asset : AccountAddress) (hstack : R.length + 43 ≤ 1024)
    (hamount : amount.toNat < 2^128) (hfree : memLoad ⟨64⟩ mem = free)
    (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 672 + 1696 * v.numAssets.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16281⟩
      (EVM.word src.val :: EVM.word recipient.val :: EVM.word asset.val :: amount :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, WithdrawCollateralTrace v src recipient asset amount evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  have hp := cometWithdrawCollateralPrefix (v := v) src recipient asset (by omega) hamount hs h
  cases he : withdrawCollateralPrefixOutcome evm src asset amount with
  | reverted => rw [he] at hp; exact ⟨.reverted, .reverted he, hp⟩
  | staticViolation => rw [he] at hp; exact ⟨.staticViolation, .staticViolation he, hp⟩
  | ok evm' =>
    rw [he] at hp
    obtain ⟨σ', aw', k', C', hs', r1⟩ := hp
    have hle : amount.toNat ≤ (withdrawCollateralBalance evm src asset).toNat := by
      by_contra hn
      simp only [withdrawCollateralPrefixOutcome, if_neg hn] at he
      cases he
    have hnext : (UInt256.sub (withdrawCollateralBalance evm src asset) amount).toNat < 2^128 := by
      rw [usub_toNat hle]
      have hb : (withdrawCollateralBalance evm src asset).toNat < 2^128 := low128_lt _
      omega
    obtain ⟨result, ht, hr⟩ := cometWithdrawCollateralTail (v := v) src recipient asset
      hstack hamount (low128_lt _) hnext (withdrawCollateralPrefixMemory_free src asset hmem hfree)
      hlo hbound hret hs' r1
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
