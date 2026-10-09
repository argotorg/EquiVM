import Benchmarks.CompoundIII.Comet.TransferBaseBalanceEvm
import Benchmarks.CompoundIII.Comet.PrincipalValueEvm
import Benchmarks.CompoundIII.Comet.WithdrawAmountsEvm
import Benchmarks.CompoundIII.Comet.RepayAmountsEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104

theorem cometTransferBasePrincipals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14798⟩
      (transferBaseBalanceStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
      mem aw rdata σ k C) :
    ((PrincipalValueFits evm (withdrawBaseBalance evm srcPrincipal amount) ∧
      PrincipalValueFits evm (supplyBaseBalance evm dstPrincipal amount)) ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨14818⟩
        (transferBasePrincipalStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
        mem aw rdata σ k' C') ∨
    (¬ (PrincipalValueFits evm (withdrawBaseBalance evm srcPrincipal amount) ∧
      PrincipalValueFits evm (supplyBaseBalance evm dstPrincipal amount)) ∧
      RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_14798 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometPrincipalValue (v := v) (by change R.length + 9 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1 with
    ⟨hsf, k2, C2, r2⟩ | ⟨hsf, hr⟩
  · have r3 := cometWithExtendedAssetList_block_14808 (immWords := wordsOf (immStore v))
      (by change R.length + 7 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    rcases cometPrincipalValue (v := v) (by change R.length + 10 + 12 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r3 with
      ⟨hdf, k4, C4, r4⟩ | ⟨hdf, hr⟩
    · exact Or.inl ⟨⟨hsf, hdf⟩, k4, C4, r4⟩
    · exact Or.inr ⟨fun hf ↦ hdf hf.2, hr⟩
  · exact Or.inr ⟨fun hf ↦ hsf hf.1, hr⟩

theorem cometTransferBaseAmounts {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨14818⟩
      (transferBasePrincipalStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
      mem aw rdata σ k C) :
    ((WithdrawAmountsFits srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount) ∧
      RepayAmountsFits dstPrincipal (supplyBasePrincipal evm dstPrincipal amount)) ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨14841⟩
        (transferBaseMathStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
        mem aw rdata σ k' C') ∨
    (¬ (WithdrawAmountsFits srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount) ∧
      RepayAmountsFits dstPrincipal (supplyBasePrincipal evm dstPrincipal amount)) ∧
      RDrev (deployedRuntime v) g s0) := by
  have r1 := cometWithExtendedAssetList_block_14818 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 12 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometWithdrawAmounts (v := v) (by change R.length + 10 + 10 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hsf, k2, C2, r2⟩ | ⟨hsf, hr⟩
  · have hsf' : WithdrawAmountsFits srcPrincipal (withdrawBasePrincipal evm srcPrincipal amount) :=
      by simpa only [WithdrawAmountsFits, signed104_signextend] using hsf
    have r3 := cometWithExtendedAssetList_block_14830 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 12 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    rcases cometRepayAmounts (v := v) (by change R.length + 10 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3 with
      ⟨hdf, k4, C4, r4⟩ | ⟨hdf, hr⟩
    · have hdf' : RepayAmountsFits dstPrincipal (supplyBasePrincipal evm dstPrincipal amount) :=
        by simpa only [RepayAmountsFits, signed104_signextend] using hdf
      refine Or.inl ⟨⟨hsf', hdf'⟩, k4, C4, ?_⟩
      simpa only [transferBaseMathStack, repayAmount, supplyAmount, withdrawBorrowAmount,
        withdrawSupplyAmount, principalDecrease, positivePrincipal, negativePrincipal,
        signed104_signextend] using r4
    · refine Or.inr ⟨?_, hr⟩
      intro hf; apply hdf
      simpa only [RepayAmountsFits, signed104_signextend] using hf.2
  · refine Or.inr ⟨?_, hr⟩
    intro hf; apply hsf
    simpa only [WithdrawAmountsFits, signed104_signextend] using hf.1

theorem cometTransferBaseMath {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14741⟩
      (UInt256.signextend (UInt256.ofNat 12) dstPrincipal :: dstPtr :: amount :: srcPtr :: src ::
        UInt256.signextend (UInt256.ofNat 12) srcPrincipal :: dst :: ret :: R)
      mem aw rdata σ k C) :
    (TransferBaseMathFits evm srcPrincipal dstPrincipal amount ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨14841⟩
        (transferBaseMathStack evm srcPrincipal dstPrincipal srcPtr dstPtr src dst amount ret R)
        mem aw rdata σ k' C') ∨
    (¬ TransferBaseMathFits evm srcPrincipal dstPrincipal amount ∧
      RDrev (deployedRuntime v) g s0) := by
  rcases cometTransferBaseBalances (by omega) hs h with ⟨hb, k1, C1, r1⟩ | ⟨hb, hr⟩
  · rcases cometTransferBasePrincipals hstack hs r1 with ⟨hp, k2, C2, r2⟩ | ⟨hp, hr⟩
    · rcases cometTransferBaseAmounts (by omega) r2 with ⟨ha, k3, C3, r3⟩ | ⟨ha, hr⟩
      · exact Or.inl ⟨⟨⟨hb.1, hp.1, ha.1⟩, hb.2, hp.2, ha.2⟩, k3, C3, r3⟩
      · exact Or.inr ⟨fun hf ↦ ha ⟨hf.1.2.2, hf.2.2.2⟩, hr⟩
    · exact Or.inr ⟨fun hf ↦ hp ⟨hf.1.2.1, hf.2.2.1⟩, hr⟩
  · exact Or.inr ⟨fun hf ↦ hb ⟨hf.1.1, hf.2.1⟩, hr⟩

end Benchmarks.CompoundIII.Comet
