import Benchmarks.UniswapV3.Pool.LiquidityDeltaInternal
import Benchmarks.UniswapV3.Pool.ReachRoutineCost
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem liquidityDeltaMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x y : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    (¬liquidityDeltaValid x y ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (liquidityDeltaValid x y ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (liquidityDeltaResult x y) :: R) mem aw rdata σ k' C') := by
  apply rdRoutine_mono rd
  intro gas start rr
  rcases liquidityDeltaCanonicalX (v := v) x y rr hxlo hxhi hylo hyhi hret hov with
    ⟨hr, hb⟩ | hgood
  · exact Or.inl ⟨hb, Or.inl hr⟩
  · exact Or.inr hgood

theorem liquidityDeltaInternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x y : Int)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int x, .int y])
    (rd : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "LiquidityMath_addDelta" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "LiquidityMath_addDelta" args retVar)
        (.ok (resumeAfterInternalCall caller retVar (some [.int (liquidityDeltaResult x y)])) evm) ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (liquidityDeltaResult x y) :: R) mem aw rdata σ k' C') := by
  have hc : {caller with locals := liquidityDeltaLocals x y} =
      liquidityDeltaFrame caller.immutables x y := by
    cases caller
    simp_all only [liquidityDeltaFrame]
  have hl : lookupCallable? caller.contract "LiquidityMath_addDelta" =
      some liquidityDeltaFunction.toCallable := by rw [hf]; exact liquidityDeltaLookup
  rcases liquidityDeltaMonoX (v := v) x y rd hxlo hxhi hylo hyhi hret hov with
    ⟨hb, hr⟩ | ⟨hv, hr⟩
  · exact Or.inl ⟨internalCallFunctionRevert he hl (liquidityDeltaBind x y)
      (by rw [hc]; exact liquidityDeltaReverts caller.immutables evm x y hb), hr⟩
  · refine Or.inr ⟨?_, hr⟩
    exact internalCallFunctionReturn (callee := liquidityDeltaFunction)
      (calleeSolm := liquidityDeltaReadyFrame caller.immutables x y)
      (value := some [.int (liquidityDeltaResult x y)]) he hl (liquidityDeltaBind x y)
      (by rw [hc]; exact liquidityDeltaReturns caller.immutables evm x y hv)

end Benchmarks.UniswapV3.Pool
