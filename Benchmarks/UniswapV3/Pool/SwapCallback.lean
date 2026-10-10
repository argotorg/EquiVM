import Benchmarks.UniswapV3.Pool.SwapCallbackCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCallbackFrame (frame : Frame) (target : AccountAddress) : Frame :=
  {frame with locals := frame.locals.insert "callback" (.address target)}

def swapCallbackDoneFrame (frame : Frame) (zeroForOne : Bool) (target : AccountAddress) : Frame :=
  {swapCallbackFrame frame target with
    locals := (swapCallbackFrame frame target).locals.insert (swapCallbackName zeroForOne) .unit}

theorem swapCallbackDoneFrame_parts (frame : Frame) (zeroForOne : Bool) (target : AccountAddress) :
    (swapCallbackDoneFrame frame zeroForOne target).contract = frame.contract ∧
    (swapCallbackDoneFrame frame zeroForOne target).immutables = frame.immutables := ⟨rfl, rfl⟩

theorem swapCallbackDoneFrame_get (frame : Frame) (zeroForOne : Bool) (target : AccountAddress)
    (name : Ident) (hn : name ≠ "callback") (hc : name ≠ swapCallbackName zeroForOne) :
    (swapCallbackDoneFrame frame zeroForOne target).locals.get? name = frame.locals.get? name := by
  simp only [swapCallbackDoneFrame, swapCallbackFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hc, Ne.symm hn, if_false]

theorem swapCallbackBody_eq (zeroForOne : Bool) :
    ((swapPaymentBody zeroForOne).drop 2).take 3 =
      (swapPaymentBody zeroForOne)[2]! :: swapCallbackStmts zeroForOne := by
  cases zeroForOne <;> rfl

theorem swapCallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {frame : Frame} {k C : Nat}
    {aw p bal junk0 junk1 junk2 junk3 junk4 len start : UInt256} {amount0 amount1 : Int}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapBalanceBeforeReturn zeroForOne)
      (bal :: junk0 :: junk1 :: junk2 :: junk3 :: junk4 :: EVM.wordOfInt amount1 ::
        EVM.wordOfInt amount0 :: len :: start :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hm : HeapMemory mem aw p)
    (hf0 : frame.locals.get? "amount0" = some (.int amount0))
    (hf1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" =
      some (.bytes (ee.calldata.extract start.toNat (start.toNat + len.toNat))))
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) (hov : R.length + 23 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config frame evm (((swapPaymentBody zeroForOne).drop 2).take 3) .reverted) ∨
    ∃ evm' σ' out aw' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm (((swapPaymentBody zeroForOne).drop 2).take 3)
        (.ok (swapCallbackDoneFrame frame zeroForOne ee.source) evm') ∧
      RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
        (⟨0⟩ :: ((p + ⟨132⟩) + UInt256.ofNat (paddedSize len.toNat)) ::
          ⟨4198899251⟩ :: EVM.word ee.source.val :: bal :: junk1 :: junk2 :: junk3 :: junk4 ::
          EVM.wordOfInt amount1 :: EVM.wordOfInt amount0 :: len :: start :: R)
        (swapCallbackMem mem p (EVM.wordOfInt amount0) (EVM.wordOfInt amount1)
          ee.calldata start len) aw' out σ' k' C' ∧
      HeapMemory (swapCallbackMem mem p (EVM.wordOfInt amount0) (EVM.wordOfInt amount1)
        ee.calldata start len) aw' p ∧
      MemoryPrefix mem (swapCallbackMem mem p (EVM.wordOfInt amount0) (EVM.wordOfInt amount1)
        ee.calldata start len) p.toNat := by
  have hlet : ExecStmt config frame evm (swapPaymentBody zeroForOne)[2]!
      (.ok (swapCallbackFrame frame ee.source) evm) := by
    cases zeroForOne <;> apply ExecStmt.letDecl <;>
      simp only [evalExpr?, pure, envValue, hs.env]
  obtain ⟨aw1, k1, C1, rd1, hm1⟩ := swapCallbackBuildX (v := v) zeroForOne rd hm hc hb hov
  rcases swapCallbackCallX (v := v) (frame := swapCallbackFrame frame ee.source) zeroForOne
      rd1 hs hperm hm1 (by simp [swapCallbackFrame])
      (by simpa [swapCallbackFrame, Std.HashMap.getElem?_insert] using hf0)
      (by simpa [swapCallbackFrame, Std.HashMap.getElem?_insert] using hf1)
      (by simpa [swapCallbackFrame, Std.HashMap.getElem?_insert] using hd)
      h0 h1 (by rw [ByteArray.size_extract]; omega) (swapCallbackMem_read _ _ _ _ _ _ _ hc hl)
      hl hb (by change R.length + 9 + 14 ≤ 1024; omega) with
    ⟨rdBad, hbad⟩ | ⟨evm', σ', out, aw', k', C', hs', hgood, rdGood, hm'⟩
  · refine Or.inl ⟨rdBad, ?_⟩
    rw [swapCallbackBody_eq]
    exact ExecBlock.consNormal hlet hbad
  · refine Or.inr ⟨evm', σ', out, aw', k', C', hs', ?_, rdGood, hm',
      callbackMem_prefix _ _ _ _ _ _ _ _ hc⟩
    rw [swapCallbackBody_eq]
    exact ExecBlock.consNormal hlet hgood

end Benchmarks.UniswapV3.Pool
