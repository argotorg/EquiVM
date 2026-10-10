import Benchmarks.CompoundIII.Comet.ApproveThisModel
import Benchmarks.CompoundIII.Comet.ApproveCallEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometApproveThisBody {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} (manager asset : AccountAddress) (amount : UInt256)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨5124⟩
      [amount, EVM.word asset.val, EVM.word manager.val] solcFreePtrMem aw rdata σ k C) :
    ∃ result, ApproveThisTrace v manager asset amount evm result ∧
      ApproveThisRun v g s0 result := by
  have hgov : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (wordsOf (immStore v) "governor") = EVM.word v.governor.val := by
    rw [wordsOf_immStore_governor]
    exact solcAddrMask_clean_left (addressWord_val_canonical v.governor)
  by_cases ha : ee.source = v.governor
  · have r1 := cometWithExtendedAssetList_block_5124_fallthrough
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [hgov, ha]; exact u256_sub_self _) h
    have hasset : UInt256.land (EVM.word asset.val)
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) = EVM.word asset.val := addressWord_val_clean asset
    by_cases hc : extCodeSizeWord σ (EVM.word asset.val) = ⟨0⟩
    · obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_5177_taken
        (immWords := wordsOf (immStore v)) (by decide) (by rw [hasset, hc]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      exact ⟨none, .codeMissing (by simpa only [hs.env] using ha)
        (by simpa only [hs.accounts] using hc),
        cometRevert1410 (by change 5 ≤ 1024; decide) r2⟩
    · obtain ⟨k2, C2, r2⟩ := cometWithExtendedAssetList_block_5177_fallthrough
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [hasset]; exact isZero_eq_zero_of_ne hc) r1
      simp only [cometWithExtendedAssetList_block_5177_fallthrough_stack, hasset] at r2
      obtain ⟨evm', z, out, hcall, hr⟩ := cometApproveCall (v := v) manager asset
        (by decide) solcFreePtrMem_mload64 (by decide) hs r2
      refine ⟨if z then some evm' else none,
        .callResult (by simpa only [hs.env] using ha)
          (by simpa only [hs.accounts] using hc) hcall, ?_⟩
      cases z <;> exact hr
  · have hn : UInt256.sub (UInt256.ofNat ee.source.val) (EVM.word v.governor.val) ≠ ⟨0⟩ := by
      intro he
      have heq := u256_sub_eq_zero_iff_eq.mp he
      change UInt256.ofNat ee.source.val = UInt256.ofNat v.governor.val at heq
      have ht := congrArg AccountAddress.ofUInt256 heq
      exact ha (by simpa only [accountAddress_roundtrip] using ht)
    have r1 := cometWithExtendedAssetList_block_5124_taken
      (immWords := wordsOf (immStore v)) (by decide) (by rw [hgov]; exact hn)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨none, .unauthorized (by simpa only [hs.env] using ha),
      cometWithExtendedAssetList_block_3682 (immWords := wordsOf (immStore v))
        (by change 7 ≤ 1024; decide) r1⟩

end Benchmarks.CompoundIII.Comet
