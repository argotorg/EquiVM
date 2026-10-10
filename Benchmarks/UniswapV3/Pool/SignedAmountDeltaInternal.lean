import Benchmarks.UniswapV3.Pool.SignedAmountDeltaSource
import Benchmarks.UniswapV3.Pool.SignedAmountDeltaTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem signedAmountDeltaInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : SignedAmountDeltaArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok
      [.int (Int.ofNat a.sqrtA.toNat), .int (Int.ofNat a.sqrtB.toNat), .int a.liquidity])
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (signedAmountDeltaEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 36 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall (signedAmountDeltaName second) args retVar) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall (signedAmountDeltaName second) args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (signedAmountDeltaResult second a)])) evm) ∧
      signedAmountDeltaValid second a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt (signedAmountDeltaResult second a) :: R) mem aw rdata σ k' C') := by
  have hc : {caller with locals := signedAmountDeltaLocals a} =
      signedAmountDeltaFrame (immStore v) a := by rw [hf]; rfl
  have hl : lookupCallable? caller.contract (signedAmountDeltaName second) =
      some (signedAmountDeltaFunction second).toCallable := by
    rw [hf]; exact signedAmountDeltaLookup second
  rcases signedAmountDeltaX (v := v) second a rd ha hret hov with ⟨hbad, rr⟩ | ⟨hv, kr, Cr, rr⟩
  · refine Or.inl ⟨?_, rr⟩
    apply internalCallFunctionRevert he hl (signedAmountDeltaBind second a)
    rw [hc]
    exact signedAmountDeltaReverts (immStore v) evm second a ha hbad
  · refine Or.inr ⟨?_, hv, kr, Cr, rr⟩
    apply internalCallFunctionReturn (callee := signedAmountDeltaFunction second)
      (calleeSolm := signedAmountDeltaReturnFrame (immStore v) second a)
      (value := some [.int (signedAmountDeltaResult second a)]) he hl (signedAmountDeltaBind second a)
    rw [hc]
    exact signedAmountDeltaReturns (immStore v) evm second a ha hv

end Benchmarks.UniswapV3.Pool
