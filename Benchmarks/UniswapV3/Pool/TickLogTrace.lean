import Benchmarks.UniswapV3.Pool.TickLogTailTrace
import Benchmarks.UniswapV3.Pool.TickLogMsbTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13989⟩ (price :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 22 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ¬ (tickLogValid (tickLogPrice price) ∧
      tickLogSafe (tickLogResult (tickLogPrice price)))) ∨
    (tickLogValid (tickLogPrice price) ∧ tickLogSafe (tickLogResult (tickLogPrice price)) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (tickLogChoiceRaw (tickLogResult (tickLogPrice price)) (tickLogPrice price) :: R)
        mem aw rdata σ k' C') := by
  rcases tickLogStartX rd (by simp only [List.length_cons]; omega) with
    ⟨rrev, hv⟩ | ⟨hv, k0, C0, rstart⟩
  · exact Or.inl ⟨rrev, fun h ↦ hv h.1⟩
  obtain ⟨k1, C1, rmsb⟩ := tickLogMsbX rstart (by simp only [List.length_cons]; omega)
  generalize hm : (tickLogMsb (tickLogPrice price)).1 = msb at rmsb
  generalize hq : tickLogRatio (tickLogPrice price) = ratio at rmsb
  generalize hr : tickLogNormalized ratio msb = r at rmsb
  have hlog : tickLogAccRun r (tickLogInitial msb) 14 = tickLogResult (tickLogPrice price) := by
    rw [tickLogResult_eq, hm, hq, hr]
  obtain ⟨k2, C2, racc⟩ := tickLogAccX rmsb (by simp only [List.length_cons]; omega)
  have hbounds := tickLogBoundsX racc (by simp only [List.length_cons]; omega)
  dsimp only at hbounds
  rw [hlog] at hbounds
  rcases hbounds with ⟨he, k3, C3, rready⟩ | ⟨he, k3, C3, rready⟩
  · have rc : RD (deployedRuntime v) ee g s0 ⟨14788⟩
        (tickLogChoiceRaw (tickLogResult (tickLogPrice price)) (tickLogPrice price) ::
          tickLogBoundsStack (tickLogResult (tickLogPrice price))
            (UInt256.ofNat msb :: tickLogScaled (tickLogRun r 13) :: ratio :: ⟨0⟩ :: price :: ret :: R))
        mem aw rdata σ k3 C3 := by
      simpa only [tickLogChoiceRaw, if_pos he] using rready
    obtain ⟨k4, C4, rout⟩ := tickLogReturnX rc hret (by omega)
    exact Or.inr ⟨hv, Or.inl he, k4, C4, rout⟩
  · rcases tickLogCallX rready he (by simp only [List.length_cons]; omega) with
      ⟨rrev, hs⟩ | ⟨hs, k4, C4, rc⟩
    · exact Or.inl ⟨rrev, fun h ↦ hs h.2⟩
    · obtain ⟨k5, C5, rout⟩ := tickLogReturnX rc hret (by omega)
      exact Or.inr ⟨hv, hs, k5, C5, rout⟩

end Benchmarks.UniswapV3.Pool
