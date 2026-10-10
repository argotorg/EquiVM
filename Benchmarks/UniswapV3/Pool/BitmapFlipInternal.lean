import Benchmarks.UniswapV3.Pool.BitmapFlipTrace
import Benchmarks.UniswapV3.Pool.TickUpdateMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapFlipInternalX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret spacingRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (caller : Frame) (evm : EVM.State) (args : List Expr) (retVar : Ident)
    (hf : caller = {contract := contract, locals := caller.locals, immutables := immStore v})
    (he : evalExprs? config caller evm args = .ok [.int tick, .int spacing])
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21285⟩
      (spacingRaw :: EVM.wordOfInt tick :: ⟨6⟩ :: ret :: R) mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hsp : -(2 ^ 23 : Int) ≤ spacing ∧ spacing < 2 ^ 23)
    (hraw : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing)
    (hm : HeapMemory mem aw p) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    (ExecStmt config caller evm (.internalCall "TickBitmap_flipTick" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm (.internalCall "TickBitmap_flipTick" args retVar) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    (ExecStmt config caller evm (.internalCall "TickBitmap_flipTick" args retVar)
      (.ok (resumeAfterInternalCall caller retVar none)
        (flipBitmap evm (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))) ∧
      ∃ k' C', SourceState s0 ee
        (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
        (flipBitmap evm (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing)) ∧
      RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing) aw rdata
        (bitmapFlippedMap σ ee (bitmapWordPos (tick.tdiv spacing)) (bitmapFlipMask tick spacing))
        k' C' ∧ HeapMemory (bitmapFlipMemory mem tick spacing) aw p) := by
  have hc : {caller with locals := bitmapFlipLocals tick spacing} =
      bitmapFlipFrame (immStore v) tick spacing := by rw [hf]; rfl
  have hl : lookupCallable? caller.contract "TickBitmap_flipTick" =
      some bitmapFlipFunction.toCallable := by rw [hf]; exact bitmapFlipLookup
  have hrevert (hb : ExecFuncBody config (bitmapFlipFrame (immStore v) tick spacing)
      evm bitmapFlipFunction.body .reverted) :
      ExecStmt config caller evm (.internalCall "TickBitmap_flipTick" args retVar) .reverted :=
    internalCallFunctionRevert he hl (bitmapFlipBind tick spacing) (by rw [hc]; exact hb)
  rcases bitmapFlipRawX (v := v) tick spacing rd ht.1 ht.2 hsp.1 hsp.2 hraw hret hov with
    ⟨hr, hz⟩ | ⟨hr, hn, hrem⟩ | ⟨hn, hrem, hb⟩
  · refine Or.inl ⟨hrevert ?_, Or.inr hr⟩
    subst spacing
    exact bitmapFlipRevertsZero (immStore v) evm tick
  · exact Or.inl ⟨hrevert (bitmapFlipRevertsRemainder (immStore v) evm tick spacing hn hrem),
      Or.inl hr⟩
  · rcases hb with ⟨hr, hp⟩ | ⟨_, k', C', r'⟩
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      apply ExecStmt.internalCallStatic he hl (bitmapFlipBind tick spacing)
      rw [hc]
      exact bitmapFlipStatic (immStore v) evm tick spacing hn hrem (by rw [hs.env]; exact hp)
    · refine Or.inr (Or.inr ⟨?_, k', C', SourceState.flipBitmap hs _ _, ?_, ?_⟩)
      · exact internalCallFunctionReturn (callee := bitmapFlipFunction)
          (calleeSolm := bitmapFlipReadyFrame (immStore v) tick spacing) (value := none)
          he hl (bitmapFlipBind tick spacing)
          (by rw [hc]; exact bitmapFlipReturns (immStore v) evm tick spacing hn hrem)
      · change RD (deployedRuntime v) ee g s0 ret R (bitmapFlipMemory mem tick spacing)
          (tickUpdateMemoryWords aw) rdata _ k' C' at r'
        rw [tickUpdateMemoryWords_eq hm.active] at r'
        exact r'
      · exact HeapMemory.twoWordHash hm _ _

end Benchmarks.UniswapV3.Pool
