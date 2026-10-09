import Benchmarks.CompoundIII.Comet.AbsorbLoopControl
import Benchmarks.CompoundIII.Comet.AbsorbLoopModel
import Benchmarks.CompoundIII.Comet.AbsorbAssetEvm
import Benchmarks.CompoundIII.Comet.InternalValueBoundedRun

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbLoop {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw free assets reserved old principal price delta ptr absorber : UInt256}
    {σ : AccountMap} {k C i : Nat} {R : List UInt256}
    (account : AccountAddress) (hstack : R.length + 27 ≤ 1024)
    (ha : assets.toNat < 2^16) (hr : reserved.toNat < 2^8) (hi : i ≤ v.numAssets.toNat)
    (hfree : memLoad ⟨64⟩ mem = free) (hlo : 96 ≤ free.toNat) (hmem : free.toNat ≤ mem.size)
    (hbound : free.toNat + 928 * (v.numAssets.toNat - i) + 256 < 2^64)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17110⟩
      (absorbLoopStack i assets reserved old principal price (EVM.word account.val) delta ptr absorber R)
      mem aw rdata σ k C) :
    ∃ result, AbsorbLoopTrace v account assets reserved i delta evm result ∧
      internalValueBoundedRun (deployedRuntime v) ee g s0 mem free
        (928 * (v.numAssets.toNat - i)) ⟨17156⟩
        (fun d ↦ absorbLoopStack v.numAssets.toNat assets reserved old principal price
          (EVM.word account.val) d ptr absorber R) result := by
  have hi8 : i < 256 := lt_of_le_of_lt hi v.numAssets_lt
  by_cases hib : i < v.numAssets.toNat
  · obtain ⟨k1, C1, r1⟩ := cometAbsorbMembership (v := v)
      (by change R.length + 7 + 10 ≤ 1024; omega) hib ha hr h
    have hi8' : i + 1 < 256 := by have hn := v.numAssets_lt; omega
    cases hmember : isInAssetBool assets (UInt256.ofNat i) reserved with
    | false =>
        rw [hmember] at r1
        obtain ⟨k2, C2, r2⟩ := cometAbsorbMemberBranch false
          (by change R.length + 10 + 2 ≤ 1024; omega) r1
        obtain ⟨k3, C3, r3⟩ := cometAbsorbIncrement
          (by change R.length + 9 + 2 ≤ 1024; omega) hi8' r2
        obtain ⟨result, ht, hrun⟩ := cometAbsorbLoop account hstack ha hr (by omega)
          hfree hlo hmem (by omega) hs r3
        exact ⟨result, .skipped hib hmember ht, hrun.mono (by omega)⟩
    | true =>
        rw [hmember] at r1
        obtain ⟨k2, C2, r2⟩ := cometAbsorbMemberBranch true
          (by change R.length + 10 + 2 ≤ 1024; omega) r1
        obtain ⟨result, ht, hrun⟩ := cometAbsorbAsset (v := v)
          (assets := reserved) (reserved := assets) account hstack
          (by rw [UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)]; exact hi8)
          hfree hlo (by omega) hs r2
        cases result with
        | reverted =>
            exact ⟨.reverted, .reverted hib hmember ht, 0, by omega, hrun⟩
        | staticViolation =>
            exact ⟨.staticViolation, .staticViolation hib hmember ht, 0, by omega, hrun⟩
        | ok evm' d =>
            obtain ⟨σ', mem', free', aw', data', k3, C3, hs', hfn, hf', hsize, hp, r3⟩ := hrun
            obtain ⟨k4, C4, r4⟩ := cometAbsorbIncrement
              (by change R.length + 9 + 2 ≤ 1024; omega) hi8' r3
            obtain ⟨result, htail, hrun⟩ := cometAbsorbLoop account hstack ha hr (by omega)
              hf' (by omega) hsize (by omega) hs' r4
            exact ⟨result, .next hib hmember ht htail, (hrun.prepend hp hfn).mono (by omega)⟩
  · have hex : v.numAssets.toNat ≤ i := by omega
    have heq : i = v.numAssets.toNat := by omega
    obtain ⟨k1, C1, r1⟩ := cometAbsorbLoopExit
      (by change R.length + 9 + 4 ≤ 1024; omega) hex hi8 h
    refine ⟨.ok evm delta, .exhausted hex, 0, by omega,
      σ, mem, free, aw, rdata, k1, C1, hs, by omega, hfree, hmem, MemoryPrefix.refl _ _, ?_⟩
    simpa only [heq] using r1
termination_by v.numAssets.toNat - i
decreasing_by all_goals omega

end Benchmarks.CompoundIII.Comet
