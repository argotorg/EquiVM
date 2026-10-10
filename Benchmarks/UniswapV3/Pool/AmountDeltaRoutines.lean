import Benchmarks.UniswapV3.Pool.Amount0DeltaSource
import Benchmarks.UniswapV3.Pool.Amount1DeltaSource
import Benchmarks.UniswapV3.Pool.Amount0DeltaTrace
import Benchmarks.UniswapV3.Pool.Amount1DeltaTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

noncomputable def amountDeltaReturnFrame (imms : Store) (second : Bool) (a : AmountDeltaArgs) : Frame :=
  if second then amount1DeltaReturnFrame imms a else amount0DeltaReturnFrame imms a

theorem amountDeltaReturns (imms : Store) (evm : EVM.State) (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : amountDeltaValid second a) :
    ExecFuncBody config (amountDeltaFrame imms a) evm (amountDeltaFunction second).body
      (.returned (amountDeltaReturnFrame imms second a) evm
        (some [.int (Int.ofNat (amountDeltaResult second a).toNat)])) := by
  cases second
  · exact amount0DeltaReturns imms evm a hfit hv
  · exact amount1DeltaReturns imms evm a hfit

theorem amountDeltaReverts (imms : Store) (evm : EVM.State) (second : Bool) (a : AmountDeltaArgs)
    (hfit : a.Fits) (hv : ¬amountDeltaValid second a) :
    ExecFuncBody config (amountDeltaFrame imms a) evm (amountDeltaFunction second).body .reverted := by
  cases second
  · exact amount0DeltaReverts imms evm a hfit hv
  · exact False.elim (hv (Or.inl rfl))

theorem amountDeltaX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : AmountDeltaArgs)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
      (amountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 30 ≤ 1024) :
    (¬amountDeltaValid second a ∧ RDrev (deployedRuntime v) g s0) ∨
      (amountDeltaValid second a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (amountDeltaResult second a :: R) mem aw rdata σ k' C') := by
  cases second
  · exact amount0DeltaX (v := v) a rd hfit hret hov
  · exact Or.inr ⟨Or.inl rfl, amount1DeltaX (v := v) a rd hfit hret (by omega)⟩

end Benchmarks.UniswapV3.Pool
