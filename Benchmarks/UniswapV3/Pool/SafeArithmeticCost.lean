import Benchmarks.UniswapV3.Pool.SafeCast256Trace
import Benchmarks.UniswapV3.Pool.SafeSignedMathTrace
import Benchmarks.UniswapV3.Pool.ReachRoutineCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem safeCast256MonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (y : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12945⟩ (y :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 5 ≤ 1024) :
    (¬safeCast256Valid y ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (safeCast256Valid y ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (y :: R) mem aw rdata σ k' C') := by
  apply rdRoutine_mono rd
  intro gas start rr
  rcases safeCast256X (v := v) y rr hret hov with ⟨hr, hb⟩ | hgood
  · exact Or.inl ⟨hb, Or.inl hr⟩
  · exact Or.inr hgood

theorem safeSignedMathMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (subtract : Bool) (x y : Int)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if subtract then 12967 else 12995))
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : -(2 ^ 255 : Int) ≤ x) (hxhi : x < 2 ^ 255)
    (hylo : -(2 ^ 255 : Int) ≤ y) (hyhi : y < 2 ^ 255)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    (¬safeSignedMathValid subtract x y ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (safeSignedMathValid subtract x y ∧ ∃ k' C', C ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (safeSignedMathResult subtract x y) :: R) mem aw rdata σ k' C') := by
  apply rdRoutine_mono rd
  intro gas start rr
  rcases safeSignedMathX (v := v) subtract x y rr hxlo hxhi hylo hyhi hret hov with
    ⟨hr, hb⟩ | hgood
  · exact Or.inl ⟨hb, Or.inl hr⟩
  · exact Or.inr hgood

end Benchmarks.UniswapV3.Pool
