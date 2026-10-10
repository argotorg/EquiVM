import Benchmarks.CompoundIII.Comet.AbsorbInternalModel
import Benchmarks.CompoundIII.Comet.AbsorbReadEvm
import Benchmarks.CompoundIII.Comet.AbsorbBasePriceEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometAbsorbReadTail {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free absorber ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 34 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : 96 ≤ mem.size)
    (hbound : free.toNat + 320 + 928 * v.numAssets.toNat + 256 < 2^64)
    (hs : SourceState s0 ee σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨16996⟩
      (EVM.word account.val :: absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbReadTrace v account evm result ∧
      internalBoundedRun (deployedRuntime v) ee g s0 free.toNat
        (free.toNat + 320 + 928 * v.numAssets.toNat) ret R result := by
  obtain ⟨aw1, k1, C1, hm, r1⟩ := cometAbsorbRead account
    (by change R.length + 2 + 11 ≤ 1024; omega) hfree hmem (by omega) hs h
  rcases cometAbsorbPresent account (by change R.length + 2 + 15 ≤ 1024; omega) hm hs r1 with
    ⟨hmin, aw2, k2, C2, r2⟩ | ⟨hmin, hrev⟩
  · have hfn : (free + (⟨160⟩ : UInt256)).toNat = free.toNat + 160 :=
      uadd_word_ofNat_toNat free 160 (by change free.toNat + 160 < 2^256; omega)
    have hf := withdrawBaseReadMemory_free mem free evm account hlo
      (by change free.toNat + 160 < 2^256; omega)
    obtain ⟨result, ht, hr⟩ := cometAbsorbBasePrice account (absorbBasic evm account) hstack hm hlo
      (by rw [hfn]) hf (by rw [hfn]; omega)
      (by rw [hfn]; exact hm.size) (by rw [hfn]; omega) hs hret r2
    exact ⟨result, .present hmin ht, hr.mono (by rw [hfn]; omega) (by rw [hfn])⟩
  · exact ⟨.reverted, .minimum hmin, hrev⟩

end Benchmarks.CompoundIII.Comet
