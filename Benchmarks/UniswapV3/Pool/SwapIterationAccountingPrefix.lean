import Benchmarks.UniswapV3.Pool.SwapIterationResultPrefix
import Benchmarks.UniswapV3.Pool.SwapIterationStoredFrameLaws
import Benchmarks.UniswapV3.Pool.SwapAccounting

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def swapIterationAccountedState (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) : SwapStateData :=
  swapAccountingState (swapExactInput a) (swapIterationStoredState v a s evm)
    (swapIterationStoredData v a s evm)

noncomputable def swapIterationAccountedFrame (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) : Frame :=
  swapAccountingFrame (swapIterationStoredFrame frame v a s evm) (swapExactInput a)
    (swapIterationStoredState v a s evm) (swapIterationStoredData v a s evm)

theorem swapIterationAccountingPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hexact : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (hm : HeapMemory mem aw q) (hs : SwapStateMemory mem p s) (ha : a.Fits) (hfit : s.Fits)
    (hpl : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 64 ≤ 1024) :
    (ExecBlock config frame evm (swapLoopBody.take 14) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 14)
        (.ok (swapIterationAccountedFrame frame v a s evm) evm) ∧
      (swapIterationAccountedState v a s evm).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3504⟩
          (q :: swapLoopWords a p (swapExactInput a).toUInt256 cache snap
            dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' (q + ⟨224⟩) ∧
        SwapStateMemory mem' p (swapIterationAccountedState v a s evm) ∧
        SwapIterationMemory mem' q (swapIterationStoredData v a s evm) ∧
        MemoryPrefix mem mem' p.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  have hbody : swapLoopBody.take 14 = swapLoopBody.take 13 ++ [swapLoopBody[13]!] := rfl
  rcases swapIterationResultPrefixX a s frame evm rd hst hf hi hstate hzero hlimit
      hm hs ha hfit hpl hdisj hb hov with
    ⟨hex1, hr⟩ | ⟨hex1, hfit1, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hc1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hex1 (by intro _ _ h; cases h)
  · rcases swapAccountingX (swapExactInput a) (swapIterationStoredState v a s evm)
        (swapIterationStoredData v a s evm) (swapIterationStoredFrame frame v a s evm) evm r1
        ((swapIterationStoredFrame_parts frame v a s evm).1.trans hf)
        (swapIterationStoredFrame_state frame v a s evm)
        (swapIterationStoredFrame_step frame v a s evm)
        ((swapIterationStoredFrame_get frame v a s evm "exactInput"
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans hexact)
        hm1 hs1 hd1 hfit1 hpl hdisj hb (by change R.length + 12 + 9 ≤ 1024; omega) with
      ⟨hex2, hr⟩ | ⟨hex2, hfit2, m2, a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [hbody]
      exact execBlock_append_ok hex1 (ExecBlock.consRevert hex2)
    · refine Or.inr ⟨?_, hfit2, m2, a2, k2, C2, by omega, r2, hm2, hs2, hd2,
        hp1.trans hp2, by omega⟩
      rw [hbody]
      exact execBlock_append_ok hex1 (ExecBlock.consNormal hex2 .nil)

end Benchmarks.UniswapV3.Pool
