import Benchmarks.CompoundIII.Comet.BuyCollateralReservesEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometBuyCollateralAfterLock {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {free base minimum : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 37 ≤ 1024) (hperm : ee.perm = true)
    (hmin : calldataWord ee.calldata 36 = minimum) (hbase : calldataWord ee.calldata 68 = base)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hb : free.toNat + 928 + 768 * v.numAssets.toNat < 2^64) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6403⟩
      (EVM.word asset.val :: EVM.word recipient.val :: R) mem aw rdata σ k C) :
    ∃ result, BuyCollateralAfterLock v asset recipient minimum base evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  have hp : pauseBitWord evm ⟨4, by decide⟩ =
      UInt256.land (UInt256.shiftRight (solcSlotWordAt ⟨1⟩ σ ee) ⟨248⟩) ⟨16⟩ := by
    rw [pauseBitWord, pauseFlagsWord_eq_shift, hs.storageRead]
    rfl
  by_cases hz : (pauseBitWord evm ⟨4, by decide⟩).toNat = 0
  · have hw := uint256_toNat_eq_zero hz
    rw [hp] at hw
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_6403_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega) hw h
    have r2 := cometWithExtendedAssetList_block_6417 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 2 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    obtain ⟨result, ht, hr⟩ := cometReservesTrace (v := v)
      (by change R.length + 2 + 35 ≤ 1024; omega) hfree hlo (by omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r2
    cases result with
    | none => exact ⟨.reverted, .failed hz ht, hr⟩
    | some r =>
      obtain ⟨evm', reserves⟩ := r
      obtain ⟨σ', mem', aw', out, k', C', hs', hf', hr⟩ := hr
      have hptr : (free + (⟨32⟩ : UInt256)).toNat = free.toNat + 32 :=
        uadd_word_ofNat_toNat free 32 (by change free.toNat + 32 < 2^256; omega)
      obtain ⟨result, hn, hr⟩ := cometBuyCollateralAfterReserves (v := v)
        (by omega) hperm hmin hbase hf' (by rw [hptr]; omega) (by rw [hptr]; omega) hs' hr
      exact ⟨result, .reserves hz ht hn, hr⟩
  · have hw : pauseBitWord evm ⟨4, by decide⟩ ≠ ⟨0⟩ := by
      intro he
      exact hz (congrArg UInt256.toNat he)
    rw [hp] at hw
    obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_6403_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega) hw
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨.reverted, .paused hz,
      cometWithExtendedAssetList_block_6727 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 3 ≤ 1024; omega) r1⟩

theorem cometBuyCollateralCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {base minimum : UInt256} {R : List UInt256}
    {asset recipient : AccountAddress}
    (hstack : R.length + 37 ≤ 1024)
    (hmin : calldataWord ee.calldata 36 = minimum) (hbase : calldataWord ee.calldata 68 = base)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6395⟩
      (EVM.word asset.val :: EVM.word recipient.val :: R) solcFreePtrMem aw rdata σ k C) :
    ∃ result, BuyCollateralTrace v asset recipient minimum base evm result ∧
      returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  have r1 := cometWithExtendedAssetList_block_6395 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometReentrancyBefore (v := v) (by change R.length + 2 + 6 ≤ 1024; omega) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases he : reentrancyOutcome evm true with
  | reverted => rw [he] at hr; exact ⟨.reverted, .reverted he, hr⟩
  | staticViolation => rw [he] at hr; exact ⟨.staticViolation, .staticViolation he, hr⟩
  | ok evm' =>
    rw [he] at hr
    obtain ⟨σ', aw', k', C', hs', r2⟩ := hr
    have hp : ee.perm = true := by
      simpa only [hs.env] using reentrancyOutcome_perm he
    have hf : memLoad ⟨64⟩ (reentrancyMemory v solcFreePtrMem) = (⟨128⟩ : UInt256) :=
      (reentrancyMemory_free v _ (by rw [solcFreePtrMem_size])).trans solcFreePtrMem_mload64
    obtain ⟨result, ht, hr⟩ := cometBuyCollateralAfterLock (v := v)
      hstack hp hmin hbase hf (by decide) (by
        have := v.numAssets_lt
        change 128 + 928 + 768 * v.numAssets.toNat < 2^64
        omega) hs' r2
    exact ⟨result, .done he ht, hr⟩

end Benchmarks.CompoundIII.Comet
