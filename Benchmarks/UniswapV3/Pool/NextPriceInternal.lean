import Benchmarks.UniswapV3.Pool.NextPriceSource
import Benchmarks.UniswapV3.Pool.NextPriceTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextPriceInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs) (caller : Frame) (evm : EVM.State)
    (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok a.values)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceEntry input)
      ((if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw ::
        priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (ha : a.Fits)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 37 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall (nextPriceName input) args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall (nextPriceName input) args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (nextPriceResult input a).toNat)])) evm) ∧
      nextPriceValid input a ∧
      UInt256.land (nextPriceRawResult input a priceRaw) (UInt256.ofNat (2 ^ 160 - 1)) =
        nextPriceResult input a ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (nextPriceRawResult input a priceRaw :: R) mem aw rdata σ k' C') := by
  have hc : {caller with locals := nextPriceLocals input a} =
      nextPriceFrame (immStore v) input a := by rw [hf]; rfl
  have hlookup : lookupCallable? caller.contract (nextPriceName input) =
      some (nextPriceFunction input).toCallable := by rw [hf]; exact nextPriceLookup input
  rcases nextPriceX (v := v) input a rd hp hl hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
  · refine Or.inl ⟨?_, hr⟩
    apply internalCallFunctionRevert he hlookup (nextPriceBind input a)
    rw [hc]
    exact nextPriceReverts (immStore v) evm input a hb
  · refine Or.inr ⟨?_, hv, nextPriceResult_clean input a priceRaw ha hv.2 hp, hr⟩
    apply internalCallFunctionReturn (callee := nextPriceFunction input)
      (calleeSolm := nextPriceResultFrame (immStore v) input a)
      (value := some [.int (Int.ofNat (nextPriceResult input a).toNat)]) he hlookup
      (nextPriceBind input a)
    rw [hc]
    exact nextPriceReturns (immStore v) evm input a ha hv

end Benchmarks.UniswapV3.Pool
