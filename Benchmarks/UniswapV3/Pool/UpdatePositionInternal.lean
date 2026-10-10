import Benchmarks.UniswapV3.Pool.UpdatePositionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem updatePositionInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args =
      .ok [.address a.owner, .int a.lower, .int a.upper, .int a.delta, .int a.current])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19151⟩
      (updatePositionEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 602 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 44 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_updatePosition" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "_updatePosition" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "_updatePosition" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some [updatePositionKeyValue a]))
        (updatePositionFinalState v a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (updatePositionFinalState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ret (solcMappingSlot ⟨7⟩ (updatePositionKey a) :: R)
        (updatePositionMemory mem p v a evm) aw' rdata σ' k' C' ∧
      HeapMemory (updatePositionMemory mem p v a evm) aw' (updatePositionFree p a evm)) := by
  have hc : {caller with locals := updatePositionLocals a} = updatePositionFrame (immStore v) a := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "_updatePosition" =
      some updatePositionFunction.toCallable := by rw [hf]; exact updatePositionLookup
  rcases updatePositionX (v := v) a evm hs rd ha hm hb hret hov with
    ⟨hsrc, hr⟩ | ⟨hsrc, hr⟩ | ⟨hsrc, hrest⟩
  · exact Or.inl ⟨internalCallFunctionRevert he hl (updatePositionBind a)
      (by rw [hc]; exact hsrc), hr⟩
  · exact Or.inr (Or.inl ⟨ExecStmt.internalCallStatic he hl (updatePositionBind a)
      (by rw [hc]; exact hsrc), hr⟩)
  · exact Or.inr (Or.inr ⟨internalCallFunctionReturn (callee := updatePositionFunction)
      (calleeSolm := updatePositionFinalFrame v a evm) (value := some [updatePositionKeyValue a])
      he hl (updatePositionBind a) (by rw [hc]; exact hsrc), hrest⟩)

end Benchmarks.UniswapV3.Pool
