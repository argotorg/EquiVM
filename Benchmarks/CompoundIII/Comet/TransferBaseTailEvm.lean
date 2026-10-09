import Benchmarks.CompoundIII.Comet.TransferBaseTailModel
import Benchmarks.CompoundIII.Comet.TransferBaseEventsEvm
import Benchmarks.CompoundIII.Comet.CollateralCheckEvm
import Benchmarks.CompoundIII.Comet.InternalDynamicOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_056

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTransferBaseTail {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free balance withdrawn supplied ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (src dst : AccountAddress) (hstack : R.length + 41 ≤ 1024)
    (hW : withdrawn.toNat < 2^104) (hS : supplied.toNat < 2^104)
    (hbalance : -(2^255 : Int) < signedWord balance) (hperm : ee.perm = true)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat)
    (hmem : 96 ≤ mem.size) (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 160 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14950⟩
      (balance :: withdrawn :: EVM.word src.val :: supplied :: EVM.word dst.val :: ret :: R)
      mem aw rdata σ k C) :
    ∃ result, TransferBaseTailTrace v src balance evm result ∧
      internalDynamicRun (deployedRuntime v) ee g s0 ret R result := by
  by_cases hn : signedWord balance < 0
  · have hcond : UInt256.slt balance (UInt256.ofNat 0) ≠ UInt256.ofNat 0 := by
      rw [signedWord_slt]
      change UInt256.fromBool (decide (signedWord balance < 0)) ≠ UInt256.ofNat 0
      rw [decide_eq_true hn]; decide
    have r1 := cometWithExtendedAssetList_block_14950_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
      hcond (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_15123
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    rcases cometNegate256 (v := v) (by change R.length + 5 + 4 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2 with
      ⟨_, _, _, r3⟩ | ⟨hbad, _⟩
    · have hmagnitude := signedWord_negativeMagnitude (le_of_lt hn)
      by_cases hm : WithdrawBaseBorrowMin v balance
      · have hle : v.baseBorrowMin.toNat ≤ (UInt256.sub (UInt256.ofNat 0) balance).toNat := by
          unfold WithdrawBaseBorrowMin at hm
          simp only [Int.ofNat_eq_natCast] at hmagnitude hm
          omega
        have r4 := cometWithExtendedAssetList_block_15132_fallthrough
          (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
          (by rw [wordsOf_immStore_baseBorrowMin, wordOfInt_ofNat_toNat]; exact ugt_zero hle) r3
        have r5 := cometWithExtendedAssetList_block_15171
          (immWords := wordsOf (immStore v)) (by change R.length + 3 + 6 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
        obtain ⟨result, ht, hr⟩ := cometCollateralCheck (v := v) true src
          (by change R.length + 6 + 35 ≤ 1024; omega) hfree hlo hmem hgap hbound
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r5
        cases result with
        | none => exact ⟨.reverted, .failed hn hm ht, hr⟩
        | some pair =>
          obtain ⟨evm', value⟩ := pair
          obtain ⟨σ', mem', free', aw', data, k', C', hs', _, hf', hlo', hb', _, r6⟩ := hr
          have r7 := cometWithExtendedAssetList_block_12096
            (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
          cases value
          · have r8 := cometWithExtendedAssetList_block_15182_taken
              (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
              (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
            exact ⟨.reverted, .rejected hn hm ht,
              cometWithExtendedAssetList_block_15192 (immWords := wordsOf (immStore v))
                (by change R.length + 5 + 3 ≤ 1024; omega) r8⟩
          · have r8 := cometWithExtendedAssetList_block_15182_fallthrough
              (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
              (by decide) r7
            have r9 := cometWithExtendedAssetList_block_15187
              (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
            obtain ⟨mem'', aw'', k'', C'', r10⟩ := cometTransferBaseEvents
              (by omega) hW hS hperm hret r9
            exact ⟨.ok evm', .accepted hn hm ht, σ', mem'', aw'', data, k'', C'', hs', r10⟩
      · have hlt : (UInt256.sub (UInt256.ofNat 0) balance).toNat < v.baseBorrowMin.toNat := by
          unfold WithdrawBaseBorrowMin at hm
          simp only [Int.ofNat_eq_natCast] at hmagnitude hm
          omega
        have r4 := cometWithExtendedAssetList_block_15132_taken
          (immWords := wordsOf (immStore v)) (by change R.length + 5 + 2 ≤ 1024; omega)
          (by rw [wordsOf_immStore_baseBorrowMin, wordOfInt_ofNat_toNat, ugt_one hlt]; decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        exact ⟨.reverted, .tooSmall hn hm,
          cometWithExtendedAssetList_block_15210 (immWords := wordsOf (immStore v))
            (by change R.length + 5 + 3 ≤ 1024; omega) r4⟩
    · exact False.elim (hbad hbalance)
  · have hcond : UInt256.slt balance (UInt256.ofNat 0) = UInt256.ofNat 0 := by
      rw [signedWord_slt]
      change UInt256.fromBool (decide (signedWord balance < 0)) = UInt256.ofNat 0
      rw [decide_eq_false hn]; rfl
    have r1 := cometWithExtendedAssetList_block_14950_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 5 + 3 ≤ 1024; omega) hcond h
    obtain ⟨mem', aw', k', C', r2⟩ := cometTransferBaseEvents (by omega) hW hS hperm hret r1
    exact ⟨.ok evm, .nonnegative (by omega), σ, mem', aw', rdata, k', C', hs, r2⟩

end Benchmarks.CompoundIII.Comet
