import Benchmarks.UniswapV3.Pool.SwapIterationPrefix
import Benchmarks.UniswapV3.Pool.SwapIterationTick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationClampedData (v : UniswapV3PoolImmutables) (a : SwapArgs) (s : SwapStateData)
    (evm : EVM.State) : SwapIterationData :=
  swapIterationTickData (swapIterationInitial s.price) (swapIterationNextTick v a s evm)
    (swapIterationInitialized v a s evm)

def swapIterationClampedFrame (frame : Frame) (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) : Frame :=
  swapIterationTickFrame (swapIterationBitmapFrame frame v a s evm)
    (swapIterationInitial s.price) (swapIterationNextTick v a s evm)
    (swapIterationInitialized v a s evm)

theorem swapIterationTickPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hst : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hstate : frame.locals.get? "state" = some s.value)
    (hzero : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hm : HeapMemory mem aw q) (hs : SwapStateMemory mem p s) (hfit : s.Fits)
    (hpl : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 34 ≤ 1024) :
    (ExecBlock config frame evm (swapLoopBody.take 6) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapLoopBody.take 6)
        (.ok (swapIterationClampedFrame frame v a s evm) evm) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3189⟩
          (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' (q + ⟨224⟩) ∧ SwapStateMemory mem' p s ∧
        SwapIterationMemory mem' q (swapIterationClampedData v a s evm) ∧
        MemoryPrefix mem mem' q.toNat ∧
        (q + UInt256.ofNat 224).toNat ≤ aw'.toNat * 32 + 32) := by
  have hbody : swapLoopBody.take 6 = swapLoopBody.take 3 ++
      (swapLoopBody.drop 3).take 3 := rfl
  rcases swapIterationPrefixX a s frame evm rd hst hf hi hstate hzero hm hs hfit hpl hdisj hb hov
      with ⟨hfail, hr⟩ | ⟨hex, ht, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hc1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hfail (by intro _ _ h; cases h)
  · obtain ⟨hex2, m2, a2, k2, C2, hC2, r2, hm2, hd2, hp2, hmono⟩ :=
      swapIterationTickX (swapIterationBitmapFrame frame v a s evm) evm
        (swapIterationInitial s.price) (swapIterationNextTick v a s evm)
        (swapIterationInitialized v a s evm) r1
        (swapIterationBitmapFrame_step frame v a s evm)
        (swapIterationBitmapFrame_tuple frame v a s evm) hm1 hd1 ht
        (swapIterationFlag_clean (swapIterationMask v a s evm))
        (swapIterationNextTick_fits v a s evm) (by have hl := hm.lower; omega) hb
        (by change R.length + 13 + 5 ≤ 1024; omega)
    refine Or.inr ⟨?_, m2, a2, k2, C2, by omega, r2, hm2, ?_, hd2, hp1.trans hp2, by omega⟩
    · rw [hbody]
      exact execBlock_append_ok hex hex2
    · exact MemoryPrefix.wordArray hp2 hs1 hpl hdisj

theorem swapIterationClampedData_bounds (v : UniswapV3PoolImmutables) (a : SwapArgs)
    (s : SwapStateData) (evm : EVM.State) :
    -887272 ≤ (swapIterationClampedData v a s evm).tickNext ∧
      (swapIterationClampedData v a s evm).tickNext ≤ 887272 :=
  swapIterationTickData_bounds _ _ _

theorem swapIterationClampedFrame_step (frame : Frame) (v : UniswapV3PoolImmutables)
    (a : SwapArgs) (s : SwapStateData) (evm : EVM.State) :
    (swapIterationClampedFrame frame v a s evm).locals.get? "step" =
      some (swapIterationClampedData v a s evm).value :=
  swapIterationTickFrame_step _ _ _ _

end Benchmarks.UniswapV3.Pool
