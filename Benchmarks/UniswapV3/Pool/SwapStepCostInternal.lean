import Benchmarks.UniswapV3.Pool.SwapStepInternal
import Benchmarks.UniswapV3.Pool.SwapStepCostTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepInternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapStepArgs) (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok a.values)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12447⟩
      (swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw ++ ret :: R)
      mem aw rdata σ k C)
    (ha : a.Fits)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hfee : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 50 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "SwapMath_computeSwapStep" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "SwapMath_computeSwapStep" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some (swapStepResults a))) evm) ∧
      swapStepValid a ∧
      UInt256.land (swapStepRawPrice a currentRaw targetRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
        swapStepPrice a ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (swapStepRawResults a currentRaw targetRaw ++ R) mem aw rdata σ k' C') := by
  have hframe : {caller with locals := swapStepLocals a} = swapStepFrame (immStore v) a := by
    rw [hf]
    rfl
  have hlookup : lookupCallable? caller.contract "SwapMath_computeSwapStep" =
      some swapStepFunction.toCallable := by rw [hf]; exact swapStepLookup
  rcases swapStepMonoX (v := v) a rd hc ht hl hfee ha hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨?_, hr⟩
    apply internalCallFunctionRevert he hlookup (swapStepBind a)
    rw [hframe]
    exact swapStepReverts (immStore v) evm a ha hb
  · refine Or.inr ⟨?_, hv,
      swapStepRawPrice_clean a currentRaw targetRaw hc ht ha hv.1.1.2.2, hr⟩
    apply internalCallFunctionReturn (callee := swapStepFunction)
      (calleeSolm := swapStepResultFrame (immStore v) a) (value := some (swapStepResults a))
      he hlookup (swapStepBind a)
    rw [hframe]
    exact swapStepReturns (immStore v) evm a ha hv

end Benchmarks.UniswapV3.Pool
