import Benchmarks.UniswapV3.Pool.OracleSurroundingResult
import Benchmarks.UniswapV3.Pool.OracleSurroundingFailure

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

abbrev OracleSurroundingOutcome (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (σ : AccountMap) (rdata : ByteArray) (ret : UInt256) (R : List UInt256)
    (time target : UInt256) (tick : Int) (index liquidity card : UInt256)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) : Prop :=
  X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    (OracleSurroundingFailure time target index card σ ee ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (index.toNat < 65535 ∧ Nonempty (OracleSurroundingExit v ee g s0 σ rdata ret R time target tick index liquidity card
      initMem initAw initFree initCost))

theorem OracleSurroundingOutcome.lift {v : UniswapV3PoolImmutables} {ee : ExecutionEnv}
    {g : Sat256} {s0 : EVM.State} {σ : AccountMap} {rdata : ByteArray} {ret : UInt256}
    {R : List UInt256} {time target index liquidity card : UInt256} {tick : Int}
    {initMem nextMem : ByteArray} {initAw initFree nextAw nextFree : UInt256}
    {initCost nextCost : Nat}
    (out : OracleSurroundingOutcome v ee g s0 σ rdata ret R time target tick index liquidity card
      nextMem nextAw nextFree nextCost)
    (hcost : initCost + (Cₘ nextAw - Cₘ initAw) ≤ nextCost)
    (hfree : initFree.toNat ≤ nextFree.toNat)
    (hpre : MemoryPrefix initMem nextMem initFree.toNat) :
    OracleSurroundingOutcome v ee g s0 σ rdata ret R time target tick index liquidity card
      initMem initAw initFree initCost := by
  rcases out with hoog | hfail | hout
  · exact Or.inl hoog
  · exact Or.inr (Or.inl hfail)
  · obtain ⟨hin, ⟨out⟩⟩ := hout
    exact Or.inr (Or.inr ⟨hin, ⟨out.lift hcost hfree hpre⟩⟩)

end Benchmarks.UniswapV3.Pool
