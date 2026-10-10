import Benchmarks.UniswapV4PoolManager.PoolSwapLoopCorrect
import Benchmarks.UniswapV4PoolManager.PoolSwapFinishTrace
import Benchmarks.UniswapV4PoolManager.BlockCorrectComposition
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapLoopReturn (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (rdata initialMem : ByteArray) (p : PoolSwapParamsWords) (step state params ret fee : UInt256)
    (R : List UInt256) (C : Nat) (post : State) (values : Option (List Value)) : Prop :=
  ∃ s r delta amount mem aw k' C', post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
    values = some (poolSwapReturnValues delta fee amount r) ∧ C ≤ C' ∧ Cₘ aw ≤ C' ∧
    RD (deployedRuntime v) I g s0 ret ([state, fee, amount, delta]++R) mem aw rdata post.accountMap k' C' ∧
    PoolSwapMemoryView mem step state params s r p ∧ r.price.toNat < 2^160 ∧ int24Canonical r.tick ∧
    r.liquidity.toNat < 2^128 ∧ MemoryWindowEq initialMem mem 64 (min step.toNat state.toNat)

theorem poolSwapFunction_loop_finish : poolSwapFunction.body.drop 28 =
    [poolSwapFunction.body[28]!] ++ poolSwapFunction.body.drop 29 := rfl

theorem poolSwapLoopFinishCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {p : PoolSwapParamsWords} {q : PoolSwapLoopWords} {old : Value}
    {aw step state params id packed ret fee protocol : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hinv : PoolSwapLoopInvariant f mem id step state params fee protocol p q)
    (hslot : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hdelta : f.locals.get? "swapDelta" = some old)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hfee : fee.toNat < 2^24) (hprotocol : protocol.toNat < 2^16)
    (hactive : PoolSwapActiveWords aw step state params) (hpaid : Cₘ aw ≤ C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨19155⟩
      (poolSwapLoopStack q p id step state params ret packed fee protocol R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecBlock config f evm (poolSwapFunction.body.drop 28) result ∧
      functionResultTrace (deployedRuntime v) g s0
        (poolSwapLoopReturn v I g s0 rdata mem p step state params ret fee R C) result := by
  rcases poolSwapLoopCorrect v hstack hI hσ0 hinv hspacing hlimit hfee hprotocol h with hog | ⟨result, hs, ht⟩
  · exact .inl hog
  rw [poolSwapFunction_loop_finish]
  apply execBlock_trace_append (execBlock_singleton hs) ht
  intro ff post _ hpost
  obtain ⟨q2, mem2, aw2, k2, C2, hC2, hI2, hσ2, rd2, hinv2, _, hw2, hsaved, hstable⟩ := hpost
  let final := poolSwapFinishResult ff post id packed q2.step q2.result p q2.remaining q2.calculated fee q2.amountToProtocol
  have hsource := poolSwapFinishSource (evm := post) hinv2.locals (hsaved.1.trans hslot) (hsaved.2.trans hdelta)
    hinv2.price hinv2.liquidity
  have htrace := poolSwapFinishTrace ff v (by omega) hI2 hinv2.memory hinv2.price hinv2.liquidity hret rd2
  refine .inr ⟨final, hsource, functionResultTrace_mono htrace ?_⟩
  intro last values hlast
  obtain ⟨hIl, hσl, hv, k3, C3, hC3, rd3⟩ := hlast
  refine ⟨q2.step, q2.result, _, q2.amountToProtocol, mem2, _, k3, C3, hIl, hσl.trans hσ2, hv, by omega,
    ?_, rd3, hinv2.memory, hinv2.price, hinv2.tick, hinv2.liquidity, hw2⟩
  rw [hstable hactive, hactive.finish]
  omega

end Benchmarks.UniswapV4PoolManager
