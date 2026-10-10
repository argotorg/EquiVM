import Benchmarks.UniswapV3.Pool.FullMathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem fullMathInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a b denominator : UInt256) (caller : Frame) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat denominator.toNat)])
    (rd : RD (deployedRuntime v) ee g s0 ⟨13017⟩ (denominator :: b :: a :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "FullMath_mulDiv" args retVar) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "FullMath_mulDiv" args retVar)
        (.ok (resumeAfterInternalCall caller retVar
          (some [.int (Int.ofNat (fullMathResult a b denominator).toNat)])) evm) ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (fullMathResult a b denominator :: R) mem aw rdata σ k' C') := by
  have hl : lookupCallable? caller.contract "FullMath_mulDiv" = some fullMathFunction.toCallable :=
    by rw [hf]; exact fullMathLookup
  have hc : {caller with locals := fullMathLocals a b denominator} =
      fullMathFrame caller.immutables a b denominator := by
    cases caller
    simp_all only [fullMathFrame]
  rcases fullMathX (v := v) rd hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨internalCallFunctionRevert he hl (fullMathBind a b denominator) ?_, hr⟩
    rw [hc]
    exact fullMathReverts caller.immutables evm a b denominator hb
  · refine Or.inr ⟨?_, hr⟩
    apply internalCallFunctionReturn (callee := fullMathFunction)
      (calleeSolm := fullMathProductFrame caller.immutables a b denominator)
      (value := some [.int (Int.ofNat (fullMathResult a b denominator).toNat)])
      he hl (fullMathBind a b denominator)
    rw [hc]
    exact fullMathReturns caller.immutables evm a b denominator hv

end Benchmarks.UniswapV3.Pool
