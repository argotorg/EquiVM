import Benchmarks.UniswapV3.Pool.TickSqrtCostTrace
import Benchmarks.UniswapV3.Pool.SwapIterationTick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationSqrtFrame (frame : Frame) (d : SwapIterationData) : Frame :=
  resumeAfterInternalCall frame "__c3"
    (some [.int (Int.ofNat (tickSqrtValue d.tickNext).toNat)])

theorem swapIterationSqrtX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (frame : Frame) (evm : EVM.State) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3189⟩ (p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (ht : -887272 ≤ d.tickNext ∧ d.tickNext ≤ 887272)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ExecStmt config frame evm swapLoopBody[6]!
      (.ok (swapIterationSqrtFrame frame d) evm) ∧
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3202⟩ (tickSqrtValue d.tickNext :: p :: R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have h24 : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23 := by omega
  have habs : d.tickNext.natAbs ≤ 887272 := by omega
  constructor
  · have htick := evalExpr_structField (name := "tickNext")
      (evalExpr_var_get (cfg := config) (evm := evm) hstep) rfl
    have he : evalExprs? config frame evm [.field (.var "step") "tickNext"] =
        .ok [.int d.tickNext] := by
      simp only [evalExprs?, htick, bind, EvalResult.bind, pure]
    exact tickSqrtInternalSource d.tickNext frame evm
      [.field (.var "step") "tickNext"] "__c3" hf he h24.1 h24.2 habs
  · have hload : memLoad (UInt256.ofNat 32 + p) mem = EVM.wordOfInt d.tickNext := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_tick hd (by change _ < 2 ^ 256; omega)
    have rr := uniswapV3Pool_block_3189 (immWords := wordsOf (immStore v)) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_3189_stack, hload] at rr
    obtain ⟨kr, Cr, hCr, rout⟩ := tickSqrtCanonicalMonoX (v := v) d.tickNext rr h24.1 h24.2 habs
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 1 + 9 ≤ 1024; omega)
    have hp32 : (UInt256.ofNat 32 + p).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)]
      omega
    refine ⟨_, kr, Cr, ?_, rout, hm.expand32 (UInt256.ofNat 32 + p) hp32,
      expandedWords_mono hm.active hp32⟩
    dsimp only [memExpansionCost] at hCr
    omega

end Benchmarks.UniswapV3.Pool
