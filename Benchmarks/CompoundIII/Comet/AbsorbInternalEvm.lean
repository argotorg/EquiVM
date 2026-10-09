import Benchmarks.CompoundIII.Comet.AbsorbReadTailEvm
import Benchmarks.CompoundIII.Comet.CollateralCheckEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_056
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free absorber ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 39 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 480 + 1856 * v.numAssets.toNat + 256 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16978⟩
      (absorber :: EVM.word account.val :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbInternalTrace v account evm result ∧
      internalBoundedRun (deployedRuntime v) ee g s0 96
        (free.toNat + 480 + 1856 * v.numAssets.toNat) ret R result := by
  have r1 := cometWithExtendedAssetList_block_16978 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨result, ht, hr⟩ := cometCollateralCheck (v := v) false account
    (by change R.length + 4 + 35 ≤ 1024; omega) hfree hlo hmem hgap (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases result with
  | none => exact ⟨.reverted, .checkReverted ht, hr⟩
  | some result =>
      obtain ⟨evm', liquidatable⟩ := result
      obtain ⟨σ1, mem1, free1, aw1, data1, k1, C1, hs1, hm1, hf1, hlo1, hhi1, hg1, r2⟩ := hr
      have r3 := cometWithExtendedAssetList_block_12096 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      cases liquidatable with
      | false =>
          have r4 := cometWithExtendedAssetList_block_16991_taken
            (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
            (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
          exact ⟨.reverted, .notLiquidatable ht,
            cometWithExtendedAssetList_block_17895 (immWords := wordsOf (immStore v))
              (by change R.length + 3 + 3 ≤ 1024; omega) r4⟩
      | true =>
          have r4 := cometWithExtendedAssetList_block_16991_fallthrough
            (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega) rfl r3
          obtain ⟨result, htail, hrun⟩ := cometAbsorbReadTail account (by omega) hf1 hlo1 hm1
            (by omega) hs1 hret r4
          exact ⟨result, .liquidatable ht htail, hrun.mono hlo1 (by omega)⟩

end Benchmarks.CompoundIII.Comet
