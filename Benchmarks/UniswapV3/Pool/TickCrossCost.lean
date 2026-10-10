import Benchmarks.UniswapV3.Pool.TickCrossInternal
import Benchmarks.UniswapV3.Pool.ReachRoutineReturnCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickCrossMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickCrossArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13596⟩
      (tickCrossWords a ++ ret :: R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23)
    (hp : ee.perm = true) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (tickNetValue (tickCrossMap a σ ee) ee a.tick) :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw)
      rdata (tickCrossMap a σ ee) k' C' :=
  rdRoutine_return_mono rd (fun _ _ rr ↦ tickCrossX (v := v) a rr ht hp hret hov)

theorem tickCrossInternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickCrossArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok a.values)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨13596⟩
      (tickCrossWords a ++ ret :: R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23)
    (hp : ee.perm = true) (hm : HeapMemory mem aw p)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ExecStmt config caller evm (.internalCall "Tick_cross" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [.int (tickCrossResult evm a)]))
        (tickCrossState evm a)) ∧
    SourceState s0 ee (tickCrossMap a σ ee) (tickCrossState evm a) ∧
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt (tickCrossResult evm a) :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw rdata (tickCrossMap a σ ee) k' C' ∧
      HeapMemory (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw p := by
  have hc : {caller with locals := tickCrossLocals a} = tickCrossFrame (immStore v) a := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "Tick_cross" = some tickCrossFunction.toCallable := by
    rw [hf]; exact tickCrossLookup
  obtain ⟨k', C', hC, rr⟩ := tickCrossMonoX (v := v) a rd ht hp hret hov
  have hs' := SourceState.tickCross hs a
  have hv : tickCrossResult evm a = tickNetValue (tickCrossMap a σ ee) ee a.tick := by
    simp only [tickCrossResult, hs'.env, ← hs'.accounts]
  refine ⟨?_, hs', k', C', hC, ?_, HeapMemory.twoWordHash hm _ _⟩
  · exact internalCallFunctionReturn (callee := tickCrossFunction)
      (calleeSolm := tickCrossResultFrame (immStore v) a evm)
      (value := some [.int (tickCrossResult evm a)]) he hl (tickCrossBind a)
      (by rw [hc]; exact tickCrossReturns (immStore v) evm a)
  · simpa only [tickUpdateMemoryWords_eq hm.active, ← hv] using rr

end Benchmarks.UniswapV3.Pool
