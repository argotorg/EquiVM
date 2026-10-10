import Benchmarks.UniswapV3.Pool.TickClearTrace
import Benchmarks.UniswapV3.Pool.TickUpdateMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickClearInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick : Int)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok [.int tick])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21964⟩
      (EVM.wordOfInt tick :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hm : HeapMemory mem aw p) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "Tick_clear" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Tick_clear" args retVar)
      (.ok (resumeAfterInternalCall caller retVar none) (tickClearState evm tick)) ∧
      ∃ k' C', SourceState s0 ee (tickClearMap σ ee tick) (tickClearState evm tick) ∧
      RD (deployedRuntime v) ee g s0 ret R (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) aw rdata
        (tickClearMap σ ee tick) k' C' ∧
      HeapMemory (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem) aw p) := by
  have hc : {caller with locals := tickClearLocals tick} = tickClearFrame (immStore v) tick := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "Tick_clear" = some tickClearFunction.toCallable := by
    rw [hf]; exact tickClearLookup
  cases hp : ee.perm
  · refine Or.inl ⟨?_, tickClearStaticX (v := v) rd hp hov⟩
    apply ExecStmt.internalCallStatic he hl (tickClearBind tick)
    rw [hc]
    exact tickClearStatic (immStore v) evm tick (by rw [hs.env]; exact hp)
  · obtain ⟨k', C', r'⟩ := tickClearWriteExactX (v := v) tick rd ht.1 ht.2 hp hret hov
    refine Or.inr ⟨?_, k', C', SourceState.tickClear hs tick, ?_, HeapMemory.twoWordHash hm _ _⟩
    · exact internalCallFunctionReturn (callee := tickClearFunction)
        (calleeSolm := tickClearFrame (immStore v) tick) (value := none)
        he hl (tickClearBind tick) (by rw [hc]; exact tickClearReturns (immStore v) evm tick)
    · change RD (deployedRuntime v) ee g s0 ret R (twoWordHashMem (EVM.wordOfInt tick) ⟨5⟩ mem)
        (tickUpdateMemoryWords aw) rdata _ k' C' at r'
      rw [tickUpdateMemoryWords_eq hm.active] at r'
      exact r'

end Benchmarks.UniswapV3.Pool
