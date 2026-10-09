import Benchmarks.CompoundIII.Comet.WithdrawInternalModel
import Benchmarks.CompoundIII.Comet.WithdrawAssetEvm
import Benchmarks.CompoundIII.Comet.WithdrawAuthEvm
import Benchmarks.CompoundIII.Comet.ReentrancyEvm
import Benchmarks.CompoundIII.Comet.AccrueAccountInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawInternalAfter {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (operator src recipient asset : AccountAddress) (hstack : R.length + 44 ≤ 1024)
    (hperm : ee.perm = true)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 672 + 1696 * v.numAssets.toNat < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15597⟩
      (EVM.word operator.val :: EVM.word src.val :: EVM.word recipient.val :: EVM.word asset.val ::
        amount :: UInt256.ofNat 2308 :: R) mem aw rdata σ k C) :
    ∃ result, WithdrawInternalAfter v operator src recipient asset amount evm result ∧
      voidOutcomeRun (deployedRuntime v) g s0 result := by
  have ha := cometWithdrawAuth (v := v) operator src recipient asset
    (by change R.length + 1 + 13 ≤ 1024; omega) hs h
  by_cases hv : WithdrawAuthValid evm operator src
  · rw [if_pos hv] at ha
    obtain ⟨_, _, _, r1⟩ := ha
    obtain ⟨result, ht, hr⟩ := cometWithdrawAsset (v := v) src recipient asset hstack
      ((permissionMemory_free _ _ hmem).trans hfree) hlo
      (by rw [permissionMemory_size_ge _ _ (by omega)]; exact hmem) hbound
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
    cases result with
    | reverted => exact ⟨.reverted, .reverted hv ht, hr⟩
    | staticViolation => exact ⟨.staticViolation, .staticViolation hv ht, hr⟩
    | ok evm' =>
      obtain ⟨σ', mem', aw', rdata', k', C', hs', r2⟩ := hr
      obtain ⟨σ'', hs'', hr⟩ := cometReentrancyAfterStop (v := v) (by omega) hperm hs' r2
      refine ⟨.ok (reentrancyState evm' false), .done hv ht (by rw [hs'.env]; exact hperm), ?_⟩
      simpa only [voidOutcomeRun, hs''.accounts] using hr
  · rw [if_neg hv] at ha
    exact ⟨.reverted, .unauthorized hv, ha⟩

theorem cometWithdrawInternalStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (operator src recipient asset : AccountAddress) (hstack : R.length + 6 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hbody : ∀ {evm' σ' aw' k' C'}, SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 ret R (reentrancyMemory v mem) aw' rdata σ' k' C' →
      ∃ result, WithdrawInternalAfter v operator src recipient asset amount evm' result ∧
        voidOutcomeRun (deployedRuntime v) g s0 result)
    (h : RD (deployedRuntime v) ee g s0 ⟨12245⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ result, WithdrawInternalTrace v operator src recipient asset amount evm result ∧
      voidOutcomeRun (deployedRuntime v) g s0 result := by
  have hr := cometReentrancyBefore (v := v) hstack hs hret h
  cases he : reentrancyOutcome evm true with
  | reverted => rw [he] at hr; exact ⟨.reverted, .reverted he, hr⟩
  | staticViolation => rw [he] at hr; exact ⟨.staticViolation, .staticViolation he, hr⟩
  | ok evm' =>
    rw [he] at hr
    obtain ⟨σ', aw', k', C', hs', r1⟩ := hr
    have hp : ee.perm = true := by
      simpa only [hs.env] using reentrancyOutcome_perm he
    obtain ⟨result, ht, hr⟩ := hbody hs' hp r1
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
