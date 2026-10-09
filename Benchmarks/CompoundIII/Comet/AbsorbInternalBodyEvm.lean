import Benchmarks.CompoundIII.Comet.AbsorbTrace
import Benchmarks.CompoundIII.Comet.AbsorbBeforePointsEvm
import Benchmarks.CompoundIII.Comet.AbsorbAfterAccountsEvm
import Benchmarks.CompoundIII.Comet.ReturnOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbBodyRun {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (addr : AccountAddress) (hstack : R.length + 47 ≤ 1024)
    (hvalid : AbsorbCalldataValid ee.calldata) (hgas : cometGasBound g.toUInt256)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨16664⟩
      (EVM.word addr.val :: absorbArrayBase ee.calldata ::
        UInt256.ofNat (absorbArrayLength ee.calldata) :: ⟨22⟩ :: R) solcFreePtrMem aw rdata σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ result, AbsorbTrace v ee.calldata addr evm result ∧
        returnOutcomeRun (deployedRuntime v) g s0 ByteArray.empty result := by
  have hn : absorbArrayLength ee.calldata < 2^64 := by
    have hh := hvalid.2.2.2.2.2.1
    change absorbArrayLength ee.calldata ≤ 2^64 - 1 at hh
    omega
  have hnword : (UInt256.ofNat (absorbArrayLength ee.calldata)).toNat < 2^64 := by
    rw [UInt256.toNat_ofNat_of_lt (lt_trans hn (by decide))]
    exact hn
  obtain hoog | ⟨startGas, result, ht, hr⟩ :=
    cometAbsorbBeforePoints (v := v) hstack hvalid hgas hs h
  · exact Or.inl hoog
  cases result with
  | reverted => exact Or.inr ⟨.reverted, .reverted ht, hr⟩
  | staticViolation => exact Or.inr ⟨.staticViolation, .staticViolation ht, hr⟩
  | ok evm' =>
    obtain ⟨σ', mem', free, aw', data', k', C', hs', hlo, hb, hfree, hmem, _, _, r1⟩ := hr
    obtain ⟨endGas, hr⟩ := cometAbsorbAfterAccounts (v := v) addr (by omega)
      hnword hfree hmem hlo (by omega) hs'
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    let result := absorbAfterAccountsOutcome evm' addr (UInt256.ofNat (absorbArrayLength ee.calldata))
      startGas endGas
    refine Or.inr ⟨result, .finished startGas endGas ht, ?_⟩
    change internalDynamicRun _ _ _ _ _ _ result at hr
    cases he : result with
    | reverted => rw [he] at hr; exact hr
    | staticViolation => rw [he] at hr; exact hr
    | ok evm'' =>
      rw [he] at hr
      obtain ⟨σ'', mem'', aw'', data'', k'', C'', hs'', r2⟩ := hr
      have hret := cometWithExtendedAssetList_block_22
        (immWords := wordsOf (immStore v)) (by omega) r2
      simpa only [returnOutcomeRun, hs''.accounts] using hret

end Benchmarks.CompoundIII.Comet
