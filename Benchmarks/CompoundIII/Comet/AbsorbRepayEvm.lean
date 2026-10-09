import Benchmarks.CompoundIII.Comet.AbsorbRepayModel
import Benchmarks.CompoundIII.Comet.AbsorbTotalsEvm
import Benchmarks.CompoundIII.Comet.RepayAmountsEvm
import Benchmarks.CompoundIII.Comet.RepayAmountsWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000
attribute [local irreducible] signed104

theorem cometAbsorbRepay {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw old next : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17306⟩ (next :: old :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ⟨17381⟩ R
      (absorbRepayOutcome evm old next) := by
  have r1 := cometWithExtendedAssetList_block_17306 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rcases cometRepayAmounts (v := v) hstack
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1 with
    ⟨hf, k2, C2, r2⟩ | ⟨hf, hr⟩
  · rw [absorbRepayOutcome, if_pos hf]
    exact cometAbsorbTotals (v := v) (by omega)
      (supplyAmount_lt old next) (repayAmount_lt hf) hs r2
  · rw [absorbRepayOutcome, if_neg hf]
    exact hr

end Benchmarks.CompoundIII.Comet
