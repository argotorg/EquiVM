import Benchmarks.UniswapV3.Pool.SwapTransfer
import Benchmarks.UniswapV3.Pool.SwapCallback
import Benchmarks.UniswapV3.Pool.SwapRepayment

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapPaymentWrites (zeroForOne : Bool) : List Ident :=
  [swapTransferName zeroForOne, swapBalanceBeforeName zeroForOne, "callback",
    swapCallbackName zeroForOne, swapBalanceAfterName zeroForOne, swapRepayName zeroForOne]

theorem swapPaymentBody_decompose (zeroForOne : Bool) :
    swapPaymentBody zeroForOne = swapTransferStmt zeroForOne :: (swapPaymentBody zeroForOne)[1]! ::
      (((swapPaymentBody zeroForOne).drop 2).take 3 ++ (swapPaymentBody zeroForOne).drop 5) := by
  cases zeroForOne <;> rfl

theorem swapPaymentSource {frame : Frame} {evm : EVM.State} {result : ExecResult}
    (zeroForOne : Bool) (hz : frame.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hex : ExecBlock config frame evm (swapPaymentBody zeroForOne) result) :
    ExecStmt config frame evm swapTransition.body[18]! result := by
  cases zeroForOne
  · exact ExecStmt.iteFalse (evalExpr_var_get hz) hex
  · exact ExecStmt.iteTrue (evalExpr_var_get hz) hex

structure SwapPaymentExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (zeroForOne : Bool) (stack : List UInt256)
    (frame : Frame) (evm : EVM.State) (initMem : ByteArray) (initFree : UInt256) where
  frame' : Frame
  evm' : EVM.State
  accounts : AccountMap
  mem : ByteArray
  rdata : ByteArray
  aw : UInt256
  free : UInt256
  k : Nat
  cost : Nat
  source : ExecStmt config frame evm swapTransition.body[18]! (.ok frame' evm')
  source_state : SourceState s0 ee accounts evm'
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  locals_get : ∀ name, name ∉ swapPaymentWrites zeroForOne →
    frame'.locals.get? name = frame.locals.get? name
  rd : RD (deployedRuntime v) ee g s0 ⟨5137⟩ stack mem aw rdata accounts k cost
  heap : HeapMemory mem aw free
  memory_prefix : MemoryPrefix initMem mem initFree.toNat
  mem_lower : 128 ≤ mem.size
  zero_mem : memLoad (UInt256.ofNat 96) mem = ⟨0⟩
  free_mono : initFree.toNat ≤ free.toNat
  free_bound : free.toNat ≤ initFree.toNat + 3 * 2 ^ 138 + 425

set_option maxHeartbeats 1000000 in
theorem swapPaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free p exactWord cache snap start len ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (amount0 amount1 : Int) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4526⟩
      ([EVM.wordOfInt amount1, EVM.wordOfInt amount0] ++
        swapLoopWords a p exactWord cache snap start len ret R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v) (hperm : ee.perm = true)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hr : frame.locals.get? "recipient" = some (.address a.recipient))
    (h0 : frame.locals.get? "amount0" = some (.int amount0))
    (h1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" =
      some (.bytes (ee.calldata.extract start.toNat (start.toNat + len.toNat))))
    (hfit0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (hfit1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hm : HeapMemory mem aw free) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hb : free.toNat + 2 ^ 140 + 1024 ≤ 2 ^ 200) (hov : R.length + 33 ≤ 1024) :
    (ExecStmt config frame evm swapTransition.body[18]! .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    Nonempty (SwapPaymentExit v ee g s0 a.zeroForOne
      (swapPaymentWords a p exactWord cache snap start len ret amount0 amount1 R)
      frame evm mem free) := by
  obtain ⟨k0, C0, r0⟩ := swapPaymentGuardX (v := v) a amount0 amount1 rd (by omega)
  rcases swapTransferX (v := v) a.zeroForOne a amount0 amount1 frame evm r0 hs hf hi hperm hr
      (by cases a.zeroForOne <;> first | exact h0 | exact h1)
      (by cases a.zeroForOne <;> first | exact hfit0 | exact hfit1)
      hm hmem hzero (by omega) hov with
    ⟨hbad, rr⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, k1, C1, hs1, hex1, r1,
      hm1, hp1, hmem1, hzero1, hlo1, hhi1⟩
  · refine Or.inl ⟨swapPaymentSource a.zeroForOne hz ?_, rr⟩
    rw [swapPaymentBody_decompose]
    exact ExecBlock.consRevert hbad
  let f1 := swapTransferFrame frame a.zeroForOne (if a.zeroForOne then amount1 else amount0)
  have hf1 : f1.contract = contract := (swapTransferFrame_parts _ _ _).1.trans hf
  have hi1 : f1.immutables = immStore v := (swapTransferFrame_parts _ _ _).2.trans hi
  have hget1 (name : Ident) (hn : name ≠ swapTransferName a.zeroForOne) :
      f1.locals.get? name = frame.locals.get? name := swapTransferFrame_get _ _ _ _ hn
  rcases swapBalanceBeforeX (v := v) a.zeroForOne f1 evm1 r1 hs1 hf1 hi1 hm1 hmem1 hzero1
      (by omega) (by change R.length + 13 + 19 ≤ 1024; omega) with
    ⟨hbad, rr⟩ | ⟨evm2, σ2, out2, mem2, aw2, p2, before, k2, C2, hs2, hex2, r2,
      hm2, hp2, hmem2, hzero2, hlo2, hhi2⟩
  · refine Or.inl ⟨swapPaymentSource a.zeroForOne hz ?_, rr⟩
    rw [swapPaymentBody_decompose]
    exact ExecBlock.consNormal hex1 (ExecBlock.consRevert hbad)
  let f2 := swapBalanceBeforeFrame f1 a.zeroForOne before
  have hf2 : f2.contract = contract := hf1
  have hi2 : f2.immutables = immStore v := hi1
  have hget2 (name : Ident) (hn : name ≠ swapBalanceBeforeName a.zeroForOne)
      (ht : name ≠ swapTransferName a.zeroForOne) :
      f2.locals.get? name = frame.locals.get? name :=
    (swapBalanceBeforeFrame_get _ _ _ _ hn).trans (hget1 name ht)
  rcases swapCallbackX (v := v) (frame := f2) a.zeroForOne r2 hs2 hperm hm2
      ((hget2 "amount0" (by cases a.zeroForOne <;> decide)
        (by cases a.zeroForOne <;> decide)).trans h0)
      ((hget2 "amount1" (by cases a.zeroForOne <;> decide)
        (by cases a.zeroForOne <;> decide)).trans h1)
      ((hget2 "data" (by cases a.zeroForOne <;> decide)
        (by cases a.zeroForOne <;> decide)).trans hd)
      hfit0 hfit1 hc hl (by omega) (by change R.length + 5 + 23 ≤ 1024; omega) with
    ⟨rr, hbad⟩ | ⟨evm3, σ3, out3, aw3, k3, C3, hs3, hex3, r3, hm3, hp3⟩
  · refine Or.inl ⟨swapPaymentSource a.zeroForOne hz ?_, rr⟩
    rw [swapPaymentBody_decompose]
    exact ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2
      (execBlock_append_term hbad (by intro _ _ he; cases he)))
  let f3 := swapCallbackDoneFrame f2 a.zeroForOne ee.source
  have hf3 : f3.contract = contract := hf2
  have hi3 : f3.immutables = immStore v := hi2
  have hget3 (name : Ident) (hc : name ≠ "callback")
      (hn : name ≠ swapCallbackName a.zeroForOne) :
      f3.locals.get? name = f2.locals.get? name := swapCallbackDoneFrame_get _ _ _ _ hc hn
  have hb3 : f3.locals.get? (swapBalanceBeforeName a.zeroForOne) =
      some (.int (Int.ofNat before.toNat)) := by
    rw [hget3 _ (by cases a.zeroForOne <;> decide) (by cases a.zeroForOne <;> decide)]
    exact swapBalanceBeforeFrame_value _ _ _
  have ha3 : f3.locals.get? (poolAmountName (!a.zeroForOne)) =
      some (.int (if a.zeroForOne then amount0 else amount1)) := by
    rw [hget3 _ (by cases a.zeroForOne <;> decide) (by cases a.zeroForOne <;> decide),
      hget2 _ (by cases a.zeroForOne <;> decide) (by cases a.zeroForOne <;> decide)]
    cases a.zeroForOne <;> first | exact h0 | exact h1
  have hmem3 : 128 ≤ (swapCallbackMem mem2 p2 (EVM.wordOfInt amount0)
      (EVM.wordOfInt amount1) ee.calldata start len).size := le_trans hmem2 hp3.size
  have hzero3 : memLoad (UInt256.ofNat 96) (swapCallbackMem mem2 p2 (EVM.wordOfInt amount0)
      (EVM.wordOfInt amount1) ee.calldata start len) = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad hp3 (UInt256.ofNat 96) (by decide) hm2.lower hmem2, hzero2]
  rcases swapRepaymentX (v := v) a.zeroForOne amount0 amount1 f3 evm3 r3 hs3 hf3 hi3 hb3 ha3
      hm3 hmem3 hzero3 (by omega) (by change R.length + 7 + 25 ≤ 1024; omega) with
    ⟨hbad, rr⟩ | ⟨evm4, σ4, out4, mem4, aw4, p4, after, k4, C4, hs4, hex4, r4,
      hm4, hp4, hmem4, hzero4, hlo4, hhi4⟩
  · refine Or.inl ⟨swapPaymentSource a.zeroForOne hz ?_, rr⟩
    rw [swapPaymentBody_decompose]
    exact ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2
      (execBlock_append_ok hex3 hbad))
  refine Or.inr ⟨{
    frame' := swapRepayFrame v (swapBalanceAfterFrame f3 a.zeroForOne after).locals
      a.zeroForOne before (if a.zeroForOne then amount0 else amount1)
    evm' := evm4, accounts := σ4, mem := mem4, rdata := out4, aw := aw4, free := p4
    k := k4, cost := C4, source_state := hs4, source := ?_
    contract_eq := hf.symm, immutables_eq := hi.symm, locals_get := ?_
    rd := r4, heap := hm4, memory_prefix := ?_, mem_lower := hmem4, zero_mem := hzero4
    free_mono := by omega, free_bound := by omega }⟩
  · apply swapPaymentSource a.zeroForOne hz
    rw [swapPaymentBody_decompose]
    exact ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2
      (execBlock_append_ok hex3 hex4))
  · intro name hn
    have hn' : name ≠ swapTransferName a.zeroForOne ∧
        name ≠ swapBalanceBeforeName a.zeroForOne ∧ name ≠ "callback" ∧
        name ≠ swapCallbackName a.zeroForOne ∧ name ≠ swapBalanceAfterName a.zeroForOne ∧
        name ≠ swapRepayName a.zeroForOne := by
      simpa only [swapPaymentWrites, List.mem_cons, List.not_mem_nil, not_or,
        not_false_eq_true, and_true] using hn
    rcases hn' with ⟨ht, hb', hc', hcb, ha', hr'⟩
    rw [swapRepayFrame_get _ _ _ _ _ _ hr', swapBalanceAfterFrame_get _ _ _ _ ha',
      hget3 name hc' hcb, hget2 name hb' ht]
  · exact hp1.trans ((hp2.mono hlo1).trans ((hp3.mono (by omega)).trans (hp4.mono (by omega))))

end Benchmarks.UniswapV3.Pool
