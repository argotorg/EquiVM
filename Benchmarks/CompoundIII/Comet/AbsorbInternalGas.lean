import Benchmarks.CompoundIII.Comet.AbsorbInternalEvm
import Benchmarks.CompoundIII.Comet.InternalCostBoundedOutcome
import Benchmarks.CompoundIII.Comet.GasBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometAbsorbInternal_cost {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free absorber ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 39 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hgap : free.toNat ≤ mem.size + 32)
    (hbound : free.toNat + 480 + 1856 * v.numAssets.toNat + 256 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16978⟩
      (absorber :: EVM.word account.val :: ret :: R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ result, AbsorbInternalTrace v account evm result ∧
        internalCostBoundedRun (deployedRuntime v) ee g s0 C 96
          (free.toNat + 480 + 1856 * v.numAssets.toNat) ret R result := by
  obtain hoog | ⟨s, hbase, hp, ht, hm, ha, hd, hσ⟩ := rd_remainingGas h
  · exact Or.inl hoog
  · have hstart := hbase.start
    rw [hp, ht, hm, ha, hd, hσ] at hstart
    obtain ⟨result, htrace, hr⟩ := cometAbsorbInternal (v := v) account hstack
      hfree hlo hmem hgap hbound (hbase.sourceIn hs) hret hstart
    exact Or.inr ⟨result, htrace, hr.fromRemaining hbase⟩

theorem absorbMemoryBound_or_outOfGas {code ee g s0 pc stk mem aw data σ k C}
    {i free assets : Nat} (hgas : cometGasBound g.toUInt256)
    (hspent : 229 * i + 214 ≤ C)
    (hfree : free ≤ 128 + i * absorbAllocationPerAccount) (hassets : assets < 256)
    (h : RD code ee g s0 pc stk mem aw data σ k C) :
    free + 480 + 1856 * assets + 256 < 2^64 ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  by_cases hC : C ≤ g.toNat
  · exact Or.inl (absorbMemoryBudget_entry
      (by simpa only [cometGasBound, Sat256.toUInt256_toNat] using hgas)
      (le_trans hspent hC) hfree hassets)
  · exact Or.inr (h.oog_of_cost_gt (by omega))

end Benchmarks.CompoundIII.Comet
