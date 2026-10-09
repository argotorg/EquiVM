import Benchmarks.CompoundIII.Comet.WithdrawBaseMathModel
import Benchmarks.CompoundIII.Comet.SignedPresentValueEvm
import Benchmarks.CompoundIII.Comet.SignedSubEvm
import Benchmarks.CompoundIII.Comet.PrincipalValueEvm
import Benchmarks.CompoundIII.Comet.WithdrawAmountsEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_048
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_072

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometWithdrawBaseMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw principal ptr recipient amount src ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨15776⟩
      (UInt256.signextend (UInt256.ofNat 12) principal :: UInt256.ofNat 15852 :: ptr ::
        recipient :: amount :: src :: ret :: R) mem aw rdata σ k C) :
    (WithdrawBaseMathFits evm principal amount ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨15820⟩
        (withdrawBaseMathStack evm principal ptr recipient amount src ret R)
        mem aw rdata σ k' C') ∨
    (¬ WithdrawBaseMathFits evm principal amount ∧ RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_15776
    (immWords := wordsOf (immStore v)) (by change R.length + 6 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometSignedPresentValue (v := v) (by change R.length + 8 + 12 ≤ 1024; omega) hs
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hm, k2, C2, r2⟩ | ⟨hm, hr⟩
  · have r3 := cometWithExtendedAssetList_block_15788
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    by_cases ha : amount.toNat < 2^255
    · obtain ⟨k4, C4, r4⟩ := cometSigned256 (v := v)
        (by change R.length + 9 + 5 ≤ 1024; omega) ha
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
      have r5 := cometWithExtendedAssetList_block_10048
        (immWords := wordsOf (immStore v)) (by change R.length + 8 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      rcases cometSignedSubNonnegRight (v := v) (by change R.length + 7 + 7 ≤ 1024; omega)
          ha (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5 with
        ⟨hb, k6, C6, r6⟩ | ⟨hb, hr⟩
      · have hbalance : WithdrawBaseBalanceFits evm principal amount :=
          ⟨hm, ha, by simpa only [withdrawBaseBalanceInt,
            signedPresentValueWord_int evm principal hm] using hb⟩
        change RD _ _ _ _ _ (withdrawBaseBalance evm principal amount ::
          UInt256.signextend (UInt256.ofNat 12) principal :: UInt256.ofNat 15852 :: ptr ::
          recipient :: amount :: src :: ret :: R) _ _ _ _ _ _ at r6
        have r7 := cometWithExtendedAssetList_block_15797
          (immWords := wordsOf (immStore v)) (by change R.length + 4 + 9 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        rcases cometPrincipalValue (v := v) (by change R.length + 10 + 12 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r7 with
          ⟨hp, k8, C8, r8⟩ | ⟨hp, hr⟩
        · have r9 := cometWithExtendedAssetList_block_15813
            (immWords := wordsOf (immStore v)) (by change R.length + 6 + 7 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
          rcases cometWithdrawAmounts (v := v) (by change R.length + 9 + 10 ≤ 1024; omega)
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9 with
            ⟨hw, k10, C10, r10⟩ | ⟨hw, hr⟩
          · have hw' : WithdrawAmountsFits principal (withdrawBasePrincipal evm principal amount) :=
              by simpa only [WithdrawAmountsFits, signed104_signextend] using hw
            refine Or.inl ⟨⟨hbalance, hp, hw'⟩, k10, C10, ?_⟩
            simpa only [withdrawBaseMathStack, withdrawBasePrincipal, withdrawBorrowAmount,
              withdrawSupplyAmount, principalDecrease, positivePrincipal, signed104_signextend]
              using r10
          · refine Or.inr ⟨?_, hr⟩
            intro hf; apply hw
            simpa only [WithdrawAmountsFits, signed104_signextend] using hf.2.2
        · exact Or.inr ⟨fun hf ↦ hp hf.2.1, hr⟩
      · refine Or.inr ⟨?_, hr⟩
        intro hf; apply hb
        simpa only [withdrawBaseBalanceInt, signedPresentValueWord_int evm principal hm]
          using hf.1.2.2
    · exact Or.inr ⟨fun hf ↦ ha hf.1.2.1, cometSigned256_revert (v := v)
        (by change R.length + 9 + 5 ≤ 1024; omega) ha r3⟩
  · exact Or.inr ⟨fun hf ↦ hm hf.1.1, hr⟩

end Benchmarks.CompoundIII.Comet
