import Benchmarks.CompoundIII.Comet.TransferBaseMathModel
import Benchmarks.CompoundIII.Comet.SignedPresentValueEvm
import Benchmarks.CompoundIII.Comet.SignedSubEvm
import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_068

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometTransferBaseBalances {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14741⟩
      (UInt256.signextend (UInt256.ofNat 12) dstPrincipal :: dstPtr :: amount :: srcPtr :: src ::
        UInt256.signextend (UInt256.ofNat 12) srcPrincipal :: dst :: ret :: R)
      mem aw rdata σ k C) :
    (TransferBaseBalanceFits evm srcPrincipal dstPrincipal amount ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨14798⟩
        (transferBaseBalanceStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
        mem aw rdata σ k' C') ∨
    (¬ TransferBaseBalanceFits evm srcPrincipal dstPrincipal amount ∧
      RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_14741 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 9 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometSignedPresentValue (v := v) (by change R.length + 8 + 12 ≤ 1024; omega) hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hsp, k2, C2, r2⟩ | ⟨hsp, hr⟩
  · have r3 := cometWithExtendedAssetList_block_14751 (immWords := wordsOf (immStore v))
      (by change R.length + 5 + 7 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    by_cases ha : amount.toNat < 2^255
    · obtain ⟨k4, C4, r4⟩ := cometSigned256 (v := v)
        (by change R.length + 9 + 5 ≤ 1024; omega) ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_14760 (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 4 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      rcases cometSignedSubNonnegRight (v := v) (by change R.length + 8 + 7 ≤ 1024; omega)
          ha (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5 with
        ⟨hsb, k6, C6, r6⟩ | ⟨hsb, hr⟩
      · have hsrc : WithdrawBaseBalanceFits evm srcPrincipal amount :=
          ⟨hsp, ha, by simpa only [withdrawBaseBalanceInt,
            signedPresentValueWord_int evm srcPrincipal hsp] using hsb⟩
        have r7 := cometWithExtendedAssetList_block_14769 (immWords := wordsOf (immStore v))
          (by change R.length + 4 + 8 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        rcases cometSignedPresentValue (v := v) (by change R.length + 9 + 12 ≤ 1024; omega) hs
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7 with
          ⟨hdp, k8, C8, r8⟩ | ⟨hdp, hr⟩
        · have r9 := cometWithExtendedAssetList_block_14779 (immWords := wordsOf (immStore v))
            (by change R.length + 8 + 4 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
          obtain ⟨k10, C10, r10⟩ := cometSigned256 (v := v)
            (by change R.length + 9 + 5 ≤ 1024; omega) ha
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9
          have r11 := cometWithExtendedAssetList_block_14789 (immWords := wordsOf (immStore v))
            (by change R.length + 8 + 4 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r10
          have hsum := cometSignedAddNonnegRight (v := v)
            (by change R.length + 8 + 8 ≤ 1024; omega) ha
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r11
          by_cases hdb : supplyBaseBalanceInt evm dstPrincipal amount < (2^255 : Int)
          · have hdb' : signedWord (signedPresentValueWord evm dstPrincipal) +
                Int.ofNat amount.toNat < (2^255 : Int) := by
              simpa only [supplyBaseBalanceInt, signedPresentValueWord_int evm dstPrincipal hdp]
                using hdb
            rw [if_pos hdb'] at hsum
            obtain ⟨k12, C12, r12⟩ := hsum
            exact Or.inl ⟨⟨hsrc, hdp, ha, hdb⟩, k12, C12, r12⟩
          · have hdb' : ¬ signedWord (signedPresentValueWord evm dstPrincipal) +
                Int.ofNat amount.toNat < (2^255 : Int) := by
              simpa only [supplyBaseBalanceInt, signedPresentValueWord_int evm dstPrincipal hdp]
                using hdb
            rw [if_neg hdb'] at hsum
            exact Or.inr ⟨fun hf ↦ hdb hf.2.2.2, hsum⟩
        · exact Or.inr ⟨fun hf ↦ hdp hf.2.1, hr⟩
      · refine Or.inr ⟨?_, hr⟩
        intro hf; apply hsb
        simpa only [withdrawBaseBalanceInt, signedPresentValueWord_int evm srcPrincipal hsp]
          using hf.1.2.2
    · exact Or.inr ⟨fun hf ↦ ha hf.1.2.1, cometSigned256_revert (v := v)
        (by change R.length + 9 + 5 ≤ 1024; omega) ha r3⟩
  · exact Or.inr ⟨fun hf ↦ hsp hf.1.1, hr⟩

end Benchmarks.CompoundIII.Comet
