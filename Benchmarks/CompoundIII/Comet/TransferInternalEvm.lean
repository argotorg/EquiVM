import Benchmarks.CompoundIII.Comet.TransferInternalModel
import Benchmarks.CompoundIII.Comet.TransferAssetEvm
import Benchmarks.CompoundIII.Comet.TransferAuthEvm
import Benchmarks.CompoundIII.Comet.ReentrancyEvm
import Benchmarks.CompoundIII.Comet.TransferPublicReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferInternalAfter {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free amount : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (returnsBool : Bool) (operator src dst asset : AccountAddress) (hstack : R.length + 44 ≤ 1024)
    (hperm : ee.perm = true)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 736 + 1696 * v.numAssets.toNat < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14496⟩
      (EVM.word operator.val :: EVM.word src.val :: EVM.word dst.val :: EVM.word asset.val ::
        amount :: transferReturnPC returnsBool :: R) mem aw rdata σ k C) :
    ∃ result, TransferInternalAfter v operator src dst asset amount evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData returnsBool) result := by
  have ha := cometTransferAuth (v := v) operator src dst asset
    (by change R.length + 1 + 13 ≤ 1024; omega) hs h
  by_cases hv : AuthorizationValid evm ⟨1, by decide⟩ operator src
  · rw [if_pos hv] at ha
    obtain ⟨_, _, _, r1⟩ := ha
    have hm (a : AccountAddress) : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (EVM.word a.val) = EVM.word a.val := solcAddrMask_clean_left (addressWord_val_canonical a)
    by_cases he : src = dst
    · have r2 := cometWithExtendedAssetList_block_14531_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
        (by rw [hm, hm, he, u256_eq_refl]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨.reverted, .selfTransfer hv he,
        cometWithExtendedAssetList_block_14646 (immWords := wordsOf (immStore v))
          (by change R.length + 6 + 3 ≤ 1024; omega) r2⟩
    · have hn : EVM.word dst.val ≠ EVM.word src.val := by
        intro hw
        have ha := congrArg AccountAddress.ofUInt256 hw
        change AccountAddress.ofUInt256 (UInt256.ofNat dst.val) =
          AccountAddress.ofUInt256 (UInt256.ofNat src.val) at ha
        simp only [accountAddress_roundtrip] at ha
        exact he ha.symm
      have r2 := cometWithExtendedAssetList_block_14531_fallthrough
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
        (by rw [hm, hm]; exact u256_eq_of_ne hn) r1
      obtain ⟨result, ht, hr⟩ := cometTransferAsset (v := v) src dst asset hstack
        ((permissionMemory_free _ _ hmem).trans hfree) hlo
        (by rw [permissionMemory_size_ge _ _ (by omega)]; exact hmem) hbound
        (transferReturnPC_valid v returnsBool) hs r2
      cases result with
      | reverted => exact ⟨.reverted, .reverted hv he ht, hr⟩
      | staticViolation => exact ⟨.staticViolation, .staticViolation hv he ht, hr⟩
      | ok evm' =>
        obtain ⟨σ', mem', aw', rdata', k', C', hs', r3⟩ := hr
        exact ⟨.ok (reentrancyState evm' false),
          .done hv he ht (by rw [hs'.env]; exact hperm),
          cometTransferPublicReturn returnsBool (by omega) hperm hs' r3⟩
  · rw [if_neg hv] at ha
    exact ⟨.reverted, .unauthorized hv, ha⟩

theorem cometTransferInternalStart {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw amount ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (returnsBool : Bool) (operator src dst asset : AccountAddress) (hstack : R.length + 6 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hbody : ∀ {evm' σ' aw' k' C'}, SourceState s0 ee σ' evm' → ee.perm = true →
      RD (deployedRuntime v) ee g s0 ret R (reentrancyMemory v mem) aw' rdata σ' k' C' →
      ∃ result, TransferInternalAfter v operator src dst asset amount evm' result ∧
        returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData returnsBool) result)
    (h : RD (deployedRuntime v) ee g s0 ⟨12245⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ result, TransferInternalTrace v operator src dst asset amount evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData returnsBool) result := by
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
