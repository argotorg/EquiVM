import Benchmarks.UniswapV3.Pool.OracleWriteMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleWriteInternalRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok
      [.int (Int.ofNat a.index.toNat), .int (Int.ofNat a.time.toNat), .int a.tick,
        .int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat a.cardinality.toNat),
        .int (Int.ofNat a.cardinalityNext.toNat)])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords {a with time := timeRaw} ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits)
    (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = a.time) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar) .reverted ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (oracleWriteResultIndex a evm).toNat),
          .int (Int.ofNat (oracleWriteResultCardinality a evm).toNat)])) (oracleWriteState a evm)) ∧
      oracleWriteValid a evm ∧ ∃ σ' aw' k' C', SourceState s0 ee σ' (oracleWriteState a evm) ∧
      RD (deployedRuntime v) ee g s0 ret
        (oracleWriteResultCardinality a evm :: oracleWriteResultIndex a evm :: R)
        (oracleWriteMemory mem p a evm) aw' rdata σ' k' C' ∧
      HeapMemory (oracleWriteMemory mem p a evm) aw' (oracleWriteFree p a evm)) := by
  have hc : {caller with locals := oracleWriteLocals a} = oracleWriteFrame (immStore v) a := by
    rw [hf]; rfl
  have hl : lookupCallable? caller.contract "Oracle_write" = some oracleWriteFunction.toCallable := by
    rw [hf]; exact oracleWriteLookup
  rcases oracleWriteRawX (v := v) a evm hs rd ha htime hm hb hret hov with ⟨rr, hbad⟩ | ⟨hv, hout⟩
  · refine Or.inl ⟨?_, rr⟩
    apply internalCallFunctionRevert he hl (oracleWriteBind a)
    rw [hc]
    exact oracleWriteSourceReverts (immStore v) evm a hbad
  · rcases hout with ⟨rr, hsame, hperm⟩ | ⟨σ', aw', kr, Cr, hs', rr, hm'⟩
    · refine Or.inr (Or.inl ⟨?_, rr⟩)
      apply ExecStmt.internalCallStatic he hl (oracleWriteBind a)
      rw [hc]
      exact oracleWriteStatic (immStore v) evm a hv.1 hsame
        (hv.2.resolve_left (by simp only [hsame]; decide)) ha (by rw [hs.env]; exact hperm)
    · refine Or.inr (Or.inr ⟨?_, hv, σ', aw', kr, Cr, hs', rr, hm'⟩)
      apply internalCallFunctionReturn (callee := oracleWriteFunction)
        (calleeSolm := oracleWriteReturnFrame (immStore v) a evm)
        (value := some [.int (Int.ofNat (oracleWriteResultIndex a evm).toNat),
          .int (Int.ofNat (oracleWriteResultCardinality a evm).toNat)]) he hl (oracleWriteBind a)
      rw [hc]
      exact oracleWriteSourceReturns (immStore v) evm a hv ha

theorem oracleWriteInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok
      [.int (Int.ofNat a.index.toNat), .int (Int.ofNat a.time.toNat), .int a.tick,
        .int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat a.cardinality.toNat),
        .int (Int.ofNat a.cardinalityNext.toNat)])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 384 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar) .reverted ∧
      RDinvalid (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "Oracle_write" args retVar)
      (.ok (resumeAfterInternalCall caller retVar
        (some [.int (Int.ofNat (oracleWriteResultIndex a evm).toNat),
          .int (Int.ofNat (oracleWriteResultCardinality a evm).toNat)])) (oracleWriteState a evm)) ∧
      oracleWriteValid a evm ∧ ∃ σ' aw' k' C', SourceState s0 ee σ' (oracleWriteState a evm) ∧
      RD (deployedRuntime v) ee g s0 ret
        (oracleWriteResultCardinality a evm :: oracleWriteResultIndex a evm :: R)
        (oracleWriteMemory mem p a evm) aw' rdata σ' k' C' ∧
      HeapMemory (oracleWriteMemory mem p a evm) aw' (oracleWriteFree p a evm)) := by
  exact oracleWriteInternalRawX (v := v) (timeRaw := a.time) a caller evm args retVar hf he hs rd ha
    (u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) ha.2.1) hm hb hret hov

end Benchmarks.UniswapV3.Pool
