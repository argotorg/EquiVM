import Benchmarks.UniswapV3.Pool.TickSqrtInitialTrace
import Benchmarks.UniswapV3.Pool.TickSqrtFactorsTrace
import Benchmarks.UniswapV3.Pool.TickSqrtTailTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem tickSqrtX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw tick ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩ (tick :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ (tickSqrtTick tick).natAbs ≤ 887272) ∨
      ((tickSqrtTick tick).natAbs ≤ 887272 ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (tickSqrtRaw (tickSqrtTick tick) :: R) mem aw rdata σ k' C') := by
  rcases tickSqrtStartX rd (by simpa only [List.length_cons] using hov) with
    hfail | ⟨hv, k0, C0, rstart⟩
  · exact Or.inl hfail
  obtain ⟨k1, C1, rinitial⟩ := tickSqrtInitialX rstart (by simp only [List.length_cons]; omega)
  obtain ⟨k2, C2, rratio⟩ := tickSqrtFactorsX rinitial (by simp only [List.length_cons]; omega)
  change RD _ _ _ _ _
    (tickSqrtRatio (UInt256.ofNat (tickSqrtTick tick).natAbs) ::
      UInt256.ofNat (tickSqrtTick tick).natAbs :: ⟨0⟩ :: tick :: ret :: R) _ _ _ _ _ _ at rratio
  have hn : tickSqrtRatio (UInt256.ofNat (tickSqrtTick tick).natAbs) ≠ ⟨0⟩ := by
    intro hz
    have h := (tickSqrtRatio_bounds (UInt256.ofNat (tickSqrtTick tick).natAbs)).1
    rw [hz] at h
    exact (by decide : ¬ 0 < (⟨0⟩ : UInt256).toNat) h
  obtain ⟨k3, C3, rinverted⟩ := tickSqrtInvertX rratio hn (by simp only [List.length_cons]; omega)
  obtain ⟨k4, C4, out⟩ := tickSqrtRoundX rinverted hret (by omega)
  exact Or.inr ⟨hv, k4, C4, out⟩

end Benchmarks.UniswapV3.Pool
