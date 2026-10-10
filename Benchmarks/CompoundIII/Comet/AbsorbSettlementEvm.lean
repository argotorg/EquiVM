import Benchmarks.CompoundIII.Comet.AbsorbSettlementModel
import Benchmarks.CompoundIII.Comet.AbsorbRepayEvm
import Benchmarks.CompoundIII.Comet.AbsorbDebtEvm
import Benchmarks.CompoundIII.Comet.AbsorbEventsEvm
import Benchmarks.CompoundIII.Comet.InternalPreservingOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
attribute [local irreducible] signed104 absorbRepayOutcome

theorem cometAbsorbSettlement {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw oldPrincipal principal old next price absorber ret free : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (account : AccountAddress) (hstack : R.length + 18 ≤ 1024)
    (hn : next.toNat < 2^255) (hp : principal.toNat < 2^103) (hperm : ee.perm = true)
    (hf : memLoad ⟨64⟩ mem = free) (hl : 96 ≤ free.toNat) (hm : free.toNat ≤ mem.size)
    (hb : free.toNat + 64 < UInt256.size) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨17261⟩
      (oldPrincipal :: old :: next :: price :: EVM.word account.val :: collateralBaseScale v ::
        principal :: absorber :: ret :: R) mem aw rdata σ k C) :
    ∃ result, AbsorbSettlementTrace v evm account oldPrincipal principal old next price result ∧
      internalPreservingRun (deployedRuntime v) ee g s0 mem free rdata ret R result := by
  obtain ⟨σ1, aw1, k1, C1, hs1, r1⟩ := cometAbsorbClear (v := v) account
    (by change R.length + 2 + 15 ≤ 1024; omega) hperm hs h
  have hsize : (absorbClearMemory mem account).size = mem.size := by
    rw [absorbClearMemory,
      twoWordHashMem_size_of_ge_64 _ _ (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; omega),
      twoWordHashMem_size_of_ge_64 _ _ (by omega)]
  have hfree : memLoad ⟨64⟩ (absorbClearMemory mem account) = free := by
    rw [absorbClearMemory,
      twoWordHashMem_load_ge _ _ (by decide)
        (by rw [twoWordHashMem_size_of_ge_64 _ _ (by omega)]; change 64 + 32 ≤ mem.size; omega),
      twoWordHashMem_load_ge _ _ (by decide) (by change 64 + 32 ≤ mem.size; omega), hf]
  have hr := cometAbsorbRepay (v := v) (by change R.length + 8 + 10 ≤ 1024; omega) hs1 r1
  cases he : absorbRepayOutcome (absorbClearState evm account) oldPrincipal principal with
  | reverted =>
    rw [he] at hr
    exact ⟨.reverted, .repayReverted he, hr⟩
  | staticViolation =>
    rw [he] at hr
    exact ⟨.staticViolation, .repayStatic he, hr⟩
  | ok totaled =>
    rw [he] at hr
    obtain ⟨σ2, k2, C2, hs2, r2⟩ := hr
    have hd := cometAbsorbDebtArithmetic (v := v)
      (by change R.length + 3 + 10 ≤ 1024; omega) hn r2
    by_cases hv : AbsorbDebtValid v old next price
    · rw [if_pos hv] at hd
      obtain ⟨k3, C3, r3⟩ := hd
      obtain ⟨mem4, aw4, k4, C4, r4, hf4, hm4⟩ := cometAbsorbEvents (v := v)
        (by omega) hp hperm hfree hl (by rw [hsize]; exact hm) hb hret r3
      exact ⟨.ok totaled, .ok totaled he hv,
        mem4, σ2, aw4, k4, C4, hs2, r4, hf4, by rwa [hsize] at hm4⟩
    · rw [if_neg hv] at hd
      exact ⟨.reverted, .debtReverted totaled he hv, hd⟩

end Benchmarks.CompoundIII.Comet
