import Benchmarks.UniswapV3.Pool.SwapCallbackTrace
import Benchmarks.UniswapV3.Pool.SwapCallbackSource
import Benchmarks.UniswapV3.Pool.CallbackCallLayout

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem swapCallbackCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {frame : Frame} {k C : Nat}
    {aw p len x1 x3 x4 x5 x6 x7 x8 selector : UInt256}
    {amount0 amount1 : Int} {target : AccountAddress}
    {mem rdata data : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackEntry zeroForOne)
      (len :: x1 :: (p + ⟨132⟩) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 ::
        selector :: EVM.word target.val :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hm : HeapMemory mem aw p)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int amount0))
    (hf1 : frame.locals.get? "amount1" = some (.int amount1))
    (hd : frame.locals.get? "data" = some (.bytes data))
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hdata : data.size = len.toNat)
    (hcd : mem.readWithPadding p.toNat (132 + paddedSize len.toNat) =
      swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1) data)
    (hl : len.toNat ≤ 2 ^ 32) (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200)
    (hov : R.length + 14 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config frame evm (swapCallbackStmts zeroForOne) .reverted) ∨
    ∃ evm' σ' out aw' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm (swapCallbackStmts zeroForOne)
        (.ok {frame with locals := frame.locals.insert (swapCallbackName zeroForOne) .unit} evm') ∧
      RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
        (⟨0⟩ :: ((p + ⟨132⟩) + UInt256.ofNat (paddedSize len.toNat)) ::
          selector :: EVM.word target.val :: R) mem aw' out σ' k' C' ∧
      HeapMemory mem aw' p := by
  obtain ⟨hsize, hsub, hbound⟩ := callbackCallRange p len hb
  have hround : UInt256.land (len + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31)) =
      UInt256.ofNat (paddedSize len.toNat) := callbackPaddedWord len hl
  by_cases hc : extCodeSizeWord σ (EVM.word target.val) = ⟨0⟩
  · exact Or.inl ⟨swapCallbackNoCodeX (v := v) zeroForOne rd hc hov,
      swapCallbackNoCode zeroForOne hs.accounts ht hc⟩
  · obtain ⟨gasArg, k1, C1, rdCall⟩ := swapCallbackGuardX (v := v) zeroForOne rd hm.load64
      (by rw [hround]) hsub hc hov
    have hsmall : (swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1)
        data).size ≤ maxReturnDataSizeByGas := by
      rw [swapCallbackCalldata_size, hdata]
      have hpad : paddedSize len.toNat ≤ len.toNat + 31 := by unfold paddedSize; omega
      have hbig : 2 ^ 32 + 163 ≤ maxReturnDataSizeByGas := by decide +kernel
      omega
    obtain ⟨evm', σ', ok, out, kCall, CCall, hcall, hs', rdAfter, hout⟩ :=
      callBridge rdCall hs hperm
        (by
          cases zeroForOne
          · immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
              (⟨5039⟩ : UInt256), (UInt8.ofNat 241), .CALL, none,
              immutableLayout_inBounds, immutableTemplate_size64)
          · immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
              (⟨4737⟩ : UInt256), (UInt8.ofNat 241), .CALL, none,
              immutableLayout_inBounds, immutableTemplate_size64))
        (by rw [hsize]; exact hcd) hsmall (by change R.length + 3 + 1 ≤ 1024; omega)
    change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word target.val)) 0
      (swapCallbackCalldata (EVM.wordOfInt amount0) (EVM.wordOfInt amount1) data)
        (ok, evm', out) at hcall
    rw [show AccountAddress.ofUInt256 (EVM.word target.val) = target from
      accountAddress_roundtrip target] at hcall
    rw [show callOutputMem mem out p (⟨0⟩ : UInt256) = mem from callOutputMem_zero mem out p]
      at rdAfter
    have hpc : (swapCallbackCallPC zeroForOne) + ⟨1⟩ = swapCallbackAfterPC zeroForOne := by
      cases zeroForOne <;> rfl
    rw [hpc] at rdAfter
    cases ok
    · exact Or.inl ⟨swapCallbackFailureX (v := v) zeroForOne rdAfter
        (by change R.length + 3 + 4 ≤ 1024; omega),
        swapCallbackReverts zeroForOne hs.accounts ht hf0 hf1 hd h0 h1 hc hcall⟩
    · obtain ⟨k', C', rdDone⟩ := swapCallbackSuccessX (v := v) zeroForOne rdAfter
        (by change R.length + 3 + 3 ≤ 1024; omega)
      refine Or.inr ⟨evm', σ', out, _, k', C', hs',
        swapCallbackReturns zeroForOne hs.accounts ht hf0 hf1 hd h0 h1 hc hcall, rdDone, ?_⟩
      refine {hm with active := ?_}
      apply callActiveWords_active (activeWords_expand32 hm.active (by decide))
      · rw [hsize]; exact hbound
      · change p.toNat + 0 ≤ _; omega

end Benchmarks.UniswapV3.Pool
