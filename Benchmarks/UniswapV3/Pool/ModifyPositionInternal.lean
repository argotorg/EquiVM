import Benchmarks.UniswapV3.Pool.ModifyPositionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok [a.value])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16233⟩ (q :: ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hq : ModifyPositionParamsMemory mem q a)
    (hqlo : 96 ≤ q.toNat) (hqp : q.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 1210 ≤ 2 ^ 200) (hperm : ee.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 50 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "_modifyPosition" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "_modifyPosition" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (∃ evm' amount0 amount1 mem' free aw' σ' k' C',
      ExecStmt config caller evm (.internalCall "_modifyPosition" args retVar)
        (.ok (resumeAfterInternalCall caller retVar
          (some [modifyPositionKeyValue a, .int amount0, .int amount1])) evm') ∧
      (-(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255) ∧
      (-(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) ∧
      SourceState s0 ee σ' evm' ∧
      RD (deployedRuntime v) ee g s0 ret
        (EVM.wordOfInt amount1 :: EVM.wordOfInt amount0 :: solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: R)
        mem' aw' rdata σ' k' C' ∧ HeapMemory mem' aw' free ∧ free.toNat ≤ p.toNat + 1210 ∧
      MemoryPrefix mem mem' p.toNat) := by
  have hc : {caller with locals := modifyPositionLocals a} = modifyPositionFrame (immStore v) a := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "_modifyPosition" =
      some modifyPositionFunction.toCallable := by rw [hf]; exact modifyPositionLookup
  rcases modifyPositionX (v := v) a evm hs rd ha hm hq hqlo hqp hb hperm hret hov with
    ⟨hsrc, hr⟩ | ⟨hsrc, hr⟩ | ⟨frame, evm', a0, a1, mem', free, aw', σ', k', C', hsrc, hrest⟩
  · exact Or.inl ⟨internalCallFunctionRevert he hl (modifyPositionBind a)
      (by rw [hc]; exact hsrc), hr⟩
  · exact Or.inr (Or.inl ⟨ExecStmt.internalCallStatic he hl (modifyPositionBind a)
      (by rw [hc]; exact hsrc), hr⟩)
  · exact Or.inr (Or.inr ⟨evm', a0, a1, mem', free, aw', σ', k', C',
      internalCallFunctionReturn (callee := modifyPositionFunction) (calleeSolm := frame)
        (value := some [modifyPositionKeyValue a, .int a0, .int a1]) he hl (modifyPositionBind a)
        (by rw [hc]; exact hsrc), hrest⟩)

end Benchmarks.UniswapV3.Pool
