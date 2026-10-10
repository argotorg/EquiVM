import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource
import Benchmarks.UniswapV3.Pool.LiquidityDeltaTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem liquidityDeltaInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (x y : Int)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok [.int x, .int y])
    (rd : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt y :: EVM.wordOfInt x :: ret :: R) mem aw rdata σ k C)
    (hxlo : 0 ≤ x) (hxhi : x < 2 ^ 128)
    (hylo : -(2 ^ 127 : Int) ≤ y) (hyhi : y < 2 ^ 127)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "LiquidityMath_addDelta" args retVar) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "LiquidityMath_addDelta" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [.int (liquidityDeltaResult x y)])) evm) ∧
      liquidityDeltaValid x y ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (liquidityDeltaResult x y) :: R) mem aw rdata σ k' C') := by
  have hc : {caller with locals := liquidityDeltaLocals x y} = liquidityDeltaFrame (immStore v) x y := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "LiquidityMath_addDelta" =
      some liquidityDeltaFunction.toCallable := by rw [hf]; exact liquidityDeltaLookup
  rcases liquidityDeltaCanonicalX (v := v) x y rd hxlo hxhi hylo hyhi hret hov with
    ⟨rr, hbad⟩ | ⟨hv, kr, Cr, rr⟩
  · refine Or.inl ⟨?_, rr⟩
    apply internalCallFunctionRevert he hl (liquidityDeltaBind x y)
    rw [hc]
    exact liquidityDeltaReverts (immStore v) evm x y hbad
  · refine Or.inr ⟨?_, hv, kr, Cr, rr⟩
    apply internalCallFunctionReturn (callee := liquidityDeltaFunction)
      (calleeSolm := liquidityDeltaReadyFrame (immStore v) x y)
      (value := some [.int (liquidityDeltaResult x y)]) he hl (liquidityDeltaBind x y)
    rw [hc]
    exact liquidityDeltaReturns (immStore v) evm x y hv

end Benchmarks.UniswapV3.Pool
