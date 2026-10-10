import Benchmarks.UniswapV3.Pool.PositionUpdateTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionUpdateInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE a.key), .int a.delta,
        .int (Int.ofNat a.growth0.toNat), .int (Int.ofNat a.growth1.toNat)])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21559⟩
      (a.growth1 :: a.growth0 :: EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
      mem aw rdata σ k C)
    (hd : -(2 ^ 127 : Int) ≤ a.delta ∧ a.delta < 2 ^ 127)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 160 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 25 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "Position_update" args retVar) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Position_update" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Position_update" args retVar)
      (.ok (resumeAfterInternalCall caller retVar none) (positionUpdateFinalState a evm)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (positionUpdateFinalState a evm) ∧
      RD (deployedRuntime v) ee g s0 ret R
        (wordArrayAllocMem mem p (positionSnapshotWords a.key σ ee)) aw' rdata σ' k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (positionSnapshotWords a.key σ ee)) aw' (p + ⟨160⟩)) := by
  have hc : {caller with locals := positionUpdateLocals a} = positionUpdateFrame (immStore v) a := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "Position_update" = some positionUpdateFunction.toCallable := by
    rw [hf]; exact positionUpdateLookup
  rcases positionUpdateX (v := v) a evm hs rd hm hb hd.1 hd.2 hret hov with
    ⟨hr, hv⟩ | ⟨hv, hp⟩
  · refine Or.inl ⟨?_, hr⟩
    apply internalCallFunctionRevert he hl (positionUpdateBind a)
    rw [hc]
    exact positionUpdateLiquidityReverts (immStore v) evm a hv
  · rcases hp with ⟨hr, hp⟩ | ⟨_, σ', k', C', aw', hs', r', hm'⟩
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      apply ExecStmt.internalCallStatic he hl (positionUpdateBind a)
      rw [hc]
      exact positionUpdateStatic (immStore v) evm a hv (by rw [hs.env]; exact hp)
    · refine Or.inr (Or.inr ⟨?_, σ', aw', k', C', hs', r', hm'⟩)
      exact internalCallFunctionReturn (callee := positionUpdateFunction)
        (calleeSolm := positionUpdateReadyFrame (immStore v) a evm) (value := none)
        he hl (positionUpdateBind a) (by rw [hc]; exact positionUpdateReturns (immStore v) evm a hv)

end Benchmarks.UniswapV3.Pool
