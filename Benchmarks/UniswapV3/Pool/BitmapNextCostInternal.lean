import Benchmarks.UniswapV3.Pool.BitmapNextInternal
import Benchmarks.UniswapV3.Pool.BitmapNextCostTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextInternalMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret spacingRaw tickRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (tick spacing : Int) (lte : Bool) (caller : Frame) (evm : EVM.State)
    (args : List Expr) (retVar : Ident) (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args = .ok [.int tick, .int spacing, .bool lte])
    (hst : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11307⟩
      ((if lte then ⟨1⟩ else ⟨0⟩) :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata σ k C)
    (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hs : -(2 ^ 23 : Int) ≤ spacing ∧ spacing < 2 ^ 23)
    (htraw : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hsraw : normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat spacingRaw.toNat) = spacing)
    (hm : HeapMemory mem aw p) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 20 ≤ 1024) :
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    let result := bitmapNextResult compressed spacing lte masked
    let resultRaw := bitmapNextResultRaw compressed spacingRaw lte masked
    (ExecStmt config caller evm
        (.internalCall "TickBitmap_nextInitializedTickWithinOneWord" args retVar) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config caller evm
        (.internalCall "TickBitmap_nextInitializedTickWithinOneWord" args retVar)
        (.ok (resumeAfterInternalCall caller retVar
          (some [.int result, .bool (decide (masked ≠ ⟨0⟩))])) evm) ∧
      UInt256.signextend (UInt256.ofNat 2) resultRaw = EVM.wordOfInt result ∧
      ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
        (bitmapNextFlag masked :: resultRaw :: R)
        (bitmapNextMemory mem compressed lte) aw rdata σ k' C' ∧
        HeapMemory (bitmapNextMemory mem compressed lte) aw p) := by
  dsimp only
  have hc : {caller with locals := bitmapNextLocals tick spacing lte} =
      bitmapNextFrame caller.immutables tick spacing lte := by
    cases caller
    simp_all only [bitmapNextFrame]
  have hl : lookupCallable? caller.contract "TickBitmap_nextInitializedTickWithinOneWord" =
      some bitmapNextFunction.toCallable := by rw [hf]; exact bitmapNextLookup
  have hsp : UInt256.signextend (UInt256.ofNat 2) spacingRaw = EVM.wordOfInt spacing := by
    rw [signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide), hsraw]
  have rde : RD (deployedRuntime v) evm.executionEnv g s0 ⟨11307⟩
      ((if lte then ⟨1⟩ else ⟨0⟩) :: spacingRaw :: tickRaw :: ⟨6⟩ :: ret :: R)
      mem aw rdata evm.accountMap k C := by rw [hst.env, ← hst.accounts]; exact rd
  rcases bitmapNextMonoX (v := v) tick spacing lte rde ht.1 ht.2 hs.1 hs.2 htraw hsp
      hm.active hret hov with
    ⟨hb, hr⟩ | ⟨hn, kr, Cr, hcost, rr⟩
  · have hz : spacing = 0 := Classical.not_not.mp hb
    refine Or.inl ⟨internalCallFunctionRevert he hl (bitmapNextBind tick spacing lte) ?_, hr⟩
    rw [hc, hz]
    exact bitmapNextRevertsZero caller.immutables evm tick lte
  · refine Or.inr ⟨?_, ?_, kr, Cr, hcost, ?_, HeapMemory.twoWordHash hm _ _⟩
    · exact internalCallFunctionReturn (callee := bitmapNextFunction)
        (calleeSolm := bitmapNextReadyFrame caller.immutables evm tick spacing lte)
        (value := some [.int (bitmapNextResult (bitmapNextCompressed tick spacing) spacing lte
          (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte)),
          .bool (decide (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte ≠ ⟨0⟩))])
        he hl (bitmapNextBind tick spacing lte)
        (by rw [hc]; exact bitmapNextReturns caller.immutables evm tick spacing lte hn)
    · rw [signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide),
        bitmapNextResultRaw_normalize _ spacing spacingRaw lte _ hsraw]
    · rw [hst.env, ← hst.accounts] at rr
      exact rr

end Benchmarks.UniswapV3.Pool
