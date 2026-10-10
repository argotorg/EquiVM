import Benchmarks.CompoundIII.Comet.SupplyBaseMathModel
import Benchmarks.CompoundIII.Comet.SignedPresentValueEvm
import Benchmarks.CompoundIII.Comet.SignedArithmeticEvm
import Benchmarks.CompoundIII.Comet.PrincipalValueEvm
import Benchmarks.CompoundIII.Comet.RepayAmountsEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_048
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometSupplyBaseMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw principal ptr sender amount dst ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 24 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hprincipal : memLoad ptr mem = UInt256.signextend (UInt256.ofNat 12) principal)
    (h : RD (deployedRuntime v) ee g s0 ⟨12495⟩
      (ptr :: ⟨12604⟩ :: amount :: sender :: ⟨12591⟩ :: dst :: ret :: R)
      mem aw rdata σ k C) :
    (SupplyBaseMathFits evm principal amount ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨12543⟩
        (supplyBaseMathStack evm principal ptr sender amount dst ret R)
        mem aw' rdata σ k' C') ∨
    (¬ SupplyBaseMathFits evm principal amount ∧ RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_12495 (immWords := wordsOf (immStore v))
    (by change R.length + 6 + 9 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_12495_stack, hprincipal, signextend104_idem] at r1
  rcases cometSignedPresentValue (v := v) (by change R.length + 12 + 12 ≤ 1024; omega) hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hm, k2, C2, r2⟩ | ⟨hm, hr⟩
  · have r3 := cometWithExtendedAssetList_block_12522 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    by_cases ha : amount.toNat < 2^255
    · obtain ⟨k4, C4, r4⟩ := cometSigned256 (v := v)
        (by change R.length + 13 + 5 ≤ 1024; omega) ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_10054 (immWords := wordsOf (immStore v))
        (by change R.length + 12 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      have hsum := cometSignedAddNonnegRight (v := v)
        (by change R.length + 11 + 8 ≤ 1024; omega) ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
      by_cases hb : supplyBaseBalanceInt evm principal amount < (2^255 : Int)
      · have hb' : signedWord (signedPresentValueWord evm principal) + Int.ofNat amount.toNat <
            (2^255 : Int) := by
          simpa only [supplyBaseBalanceInt, signedPresentValueWord_int evm principal hm] using hb
        rw [if_pos hb'] at hsum
        obtain ⟨k6, C6, r6⟩ := hsum
        have hbalance : SupplyBaseBalanceFits evm principal amount := ⟨hm, ha, hb⟩
        have r7 := cometWithExtendedAssetList_block_12531 (immWords := wordsOf (immStore v))
          (by change R.length + 12 + 1 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        rcases cometPrincipalValue (v := v) (by change R.length + 10 + 12 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r7 with
          ⟨hp, k8, C8, r8⟩ | ⟨hp, hr⟩
        · have r9 := cometWithExtendedAssetList_block_12536 (immWords := wordsOf (immStore v))
            (by change R.length + 6 + 7 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
          rcases cometRepayAmounts (v := v) (by change R.length + 9 + 10 ≤ 1024; omega)
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9 with
            ⟨hw, k10, C10, r10⟩ | ⟨hw, hr⟩
          · have hw' : RepayAmountsFits principal (supplyBasePrincipal evm principal amount) :=
              by simpa only [RepayAmountsFits, signed104_signextend] using hw
            refine Or.inl ⟨⟨hbalance, hp, hw'⟩, M aw ptr ⟨32⟩, k10, C10, ?_⟩
            simpa only [supplyBaseMathStack, supplyBasePrincipal, supplyBaseBalance, repayAmount,
              supplyAmount, principalDecrease, negativePrincipal, signed104_signextend] using r10
          · refine Or.inr ⟨?_, hr⟩
            intro hf; apply hw
            simpa only [RepayAmountsFits, signed104_signextend] using hf.2.2
        · exact Or.inr ⟨fun hf ↦ hp hf.2.1, hr⟩
      · have hb' : ¬ signedWord (signedPresentValueWord evm principal) + Int.ofNat amount.toNat <
            (2^255 : Int) := by
          simpa only [supplyBaseBalanceInt, signedPresentValueWord_int evm principal hm] using hb
        rw [if_neg hb'] at hsum
        exact Or.inr ⟨fun hf ↦ hb hf.1.2.2, hsum⟩
    · exact Or.inr ⟨fun hf ↦ ha hf.1.2.1, cometSigned256_revert (v := v)
        (by change R.length + 13 + 5 ≤ 1024; omega) ha r3⟩
  · exact Or.inr ⟨fun hf ↦ hm hf.1.1, hr⟩

end Benchmarks.CompoundIII.Comet
