import Benchmarks.UniswapV3.Pool.NextSqrt0Source
import Benchmarks.UniswapV3.Pool.NextSqrt0Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0InternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs) (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok a.values)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19939⟩
      ((if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 31 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall (nextSqrtName false) args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall (nextSqrtName false) args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (nextSqrt0Result a).toNat)])) evm) ∧
      nextSqrt0Valid a ∧
      UInt256.land (nextSqrt0RawResult a priceRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
        nextSqrt0Result a ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (nextSqrt0RawResult a priceRaw :: R) mem aw rdata σ k' C') := by
  have hc : {caller with locals := nextSqrtLocals a} = nextSqrtFrame (immStore v) a := by
    rw [hf]; rfl
  have hlookup : lookupCallable? caller.contract (nextSqrtName false) =
      some (nextSqrtFunction false).toCallable := by rw [hf]; exact nextSqrtLookup false
  rcases nextSqrt0X (v := v) a rd hp hl hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨?_, hr⟩
    apply internalCallFunctionRevert he hlookup (nextSqrtBind false a)
    rw [hc]
    exact nextSqrt0Reverts (immStore v) evm a hb
  · refine Or.inr ⟨?_, hv, nextSqrt0Result_clean a priceRaw hp, hr⟩
    apply internalCallFunctionReturn (callee := nextSqrtFunction false)
      (calleeSolm := nextSqrt0FinalFrame (immStore v) a)
      (value := some [.int (Int.ofNat (nextSqrt0Result a).toNat)]) he hlookup (nextSqrtBind false a)
    rw [hc]
    exact nextSqrt0Returns (immStore v) evm a hv

end Benchmarks.UniswapV3.Pool
