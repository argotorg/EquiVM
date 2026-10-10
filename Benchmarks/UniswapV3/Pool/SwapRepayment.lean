import Benchmarks.UniswapV3.Pool.SwapRepaymentSource
import Benchmarks.UniswapV3.Pool.SwapRepayMathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapRepayFrame_get (v : UniswapV3PoolImmutables) (locals : Store)
    (zeroForOne : Bool) (before : UInt256) (amount : Int) (name : Ident)
    (hn : name ≠ swapRepayName zeroForOne) :
    (swapRepayFrame v locals zeroForOne before amount).locals.get? name = locals.get? name := by
  simp only [swapRepayFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hn, if_false]

theorem swapRepaymentBody_eq (zeroForOne : Bool) :
    (swapPaymentBody zeroForOne).drop 5 =
      (swapPaymentBody zeroForOne)[5]! :: swapRepayTailStmts zeroForOne := by
  cases zeroForOne <;> rfl

theorem swapRepaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw free before p exactWord cache snap junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool) (amount0 amount1 : Int) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
      ([junk0, junk1, junk2, junk3, before, p, exactWord, cache, snap,
        EVM.wordOfInt amount1, EVM.wordOfInt amount0] ++ R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hbefore : frame.locals.get? (swapBalanceBeforeName zeroForOne) =
      some (.int (Int.ofNat before.toNat)))
    (hamount : frame.locals.get? (poolAmountName (!zeroForOne)) =
      some (.int (if zeroForOne then amount0 else amount1)))
    (hm : HeapMemory mem aw free) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : free.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) (hov : R.length + 25 ≤ 1024) :
    (ExecBlock config frame evm ((swapPaymentBody zeroForOne).drop 5) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ evm' σ' out mem' aw' next after k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm ((swapPaymentBody zeroForOne).drop 5)
        (.ok (swapRepayFrame v (swapBalanceAfterFrame frame zeroForOne after).locals
          zeroForOne before (if zeroForOne then amount0 else amount1)) evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨5137⟩
        ([p, exactWord, cache, snap, EVM.wordOfInt amount1, EVM.wordOfInt amount0] ++ R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' free.toNat ∧
      128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      free.toNat ≤ next.toNat ∧ next.toNat ≤ free.toNat + 2 ^ 138 + 131 := by
  rcases swapBalanceAfterX (v := v) zeroForOne frame evm rd hs hf hi hm hmem hzero hb
      (by change R.length + 7 + 18 ≤ 1024; omega) with
    ⟨hbad, rr⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, value, k1, C1, hs1, hcall, r1,
      hm1, hprefix, hmem1, hzero1, hlo, hhi⟩
  · refine Or.inl ⟨?_, rr⟩
    rw [swapRepaymentBody_eq]
    exact ExecBlock.consRevert hbad
  let f1 := swapBalanceAfterFrame frame zeroForOne value
  have hf1 : f1.contract = contract := hf
  have hi1 : f1.immutables = immStore v := hi
  have hb1 : f1.locals.get? (swapBalanceBeforeName zeroForOne) =
      some (.int (Int.ofNat before.toNat)) := by
    rw [swapBalanceAfterFrame_get _ _ _ _ (by cases zeroForOne <;> decide)]
    exact hbefore
  have ha1 : f1.locals.get? (poolAmountName (!zeroForOne)) =
      some (.int (if zeroForOne then amount0 else amount1)) := by
    rw [swapBalanceAfterFrame_get _ _ _ _ (by cases zeroForOne <;> decide)]
    exact hamount
  have hr1 : f1.locals.get? (swapBalanceAfterName zeroForOne) =
      some (.int (Int.ofNat value.toNat)) := swapBalanceAfterFrame_value _ _ _
  have hword : EVM.wordOfInt (if zeroForOne then amount0 else amount1) =
      (if zeroForOne then EVM.wordOfInt amount0 else EVM.wordOfInt amount1) := by
    cases zeroForOne <;> rfl
  rcases swapRepayMathX (v := v) zeroForOne r1 (by omega) with
    ⟨hbad, rr⟩ | ⟨hgood, k2, C2, r2⟩
  · have hx := swapRepayReverts v f1.locals evm1 zeroForOne before value
      (if zeroForOne then amount0 else amount1) hb1 ha1 hr1 (by rwa [hword])
    rw [← frame_eq_of_parts hf1 hi1] at hx
    refine Or.inl ⟨?_, rr⟩
    rw [swapRepaymentBody_eq]
    exact ExecBlock.consNormal hcall hx
  · have hx := swapRepayReturns v f1.locals evm1 zeroForOne before value
      (if zeroForOne then amount0 else amount1) hb1 ha1 hr1 (by rwa [hword])
    rw [← frame_eq_of_parts hf1 hi1] at hx
    refine Or.inr ⟨evm1, σ1, out1, mem1, aw1, p1, value, k2, C2, hs1, ?_, r2,
      hm1, hprefix, hmem1, hzero1, hlo, hhi⟩
    rw [swapRepaymentBody_eq]
    exact ExecBlock.consNormal hcall hx

end Benchmarks.UniswapV3.Pool
