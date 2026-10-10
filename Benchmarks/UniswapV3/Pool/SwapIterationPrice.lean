import Benchmarks.UniswapV3.Pool.SwapIterationSqrt
import Benchmarks.UniswapV3.Pool.SwapIterationPriceStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationPriceData (d : SwapIterationData) : SwapIterationData :=
  {d with priceNext := tickSqrtValue d.tickNext}

def swapIterationPriceFrame (frame : Frame) (d : SwapIterationData) : Frame :=
  swapIterationFrame (swapIterationSqrtFrame frame d) (swapIterationPriceData d)

theorem swapIterationSqrtFrame_step {frame : Frame} (d : SwapIterationData)
    (h : frame.locals.get? "step" = some d.value) :
    (swapIterationSqrtFrame frame d).locals.get? "step" = some d.value := by
  simpa only [swapIterationSqrtFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, ↓reduceIte] using h

theorem swapIterationSqrtFrame_result (frame : Frame) (d : SwapIterationData) :
    (swapIterationSqrtFrame frame d).locals.get? "__c3" =
      some (.int (Int.ofNat (tickSqrtValue d.tickNext).toNat)) :=
  Std.HashMap.getElem?_insert_self

theorem swapIterationPriceFrame_step (frame : Frame) (d : SwapIterationData) :
    (swapIterationPriceFrame frame d).locals.get? "step" = some (swapIterationPriceData d).value :=
  Std.HashMap.getElem?_insert_self

theorem swapIterationPriceFrame_get (frame : Frame) (d : SwapIterationData) (name : Ident)
    (hs : name ≠ "step") (hc : name ≠ "__c3") :
    (swapIterationPriceFrame frame d).locals.get? name = frame.locals.get? name := by
  simp only [swapIterationPriceFrame, swapIterationFrame, swapIterationSqrtFrame,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hs, Ne.symm hc, if_false]

theorem swapIterationPriceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3189⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (ht : -887272 ≤ d.tickNext ∧ d.tickNext ≤ 887272)
    (hq : 96 ≤ q.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 23 ≤ 1024) :
    ExecBlock config frame evm ((swapLoopBody.drop 6).take 2)
      (.ok (swapIterationPriceFrame frame d) evm) ∧
    ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if a.zeroForOne then ⟨3260⟩ else ⟨3231⟩)
        ([s.price, ⟨3347⟩, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free ∧ SwapStateMemory mem' p s ∧
      SwapIterationMemory mem' q (swapIterationPriceData d) ∧
      MemoryPrefix mem mem' q.toNat ∧ aw.toNat ≤ aw'.toNat := by
  obtain ⟨hex1, a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapIterationSqrtX frame evm d rd hf hstep hm hd ht hb
      (by change R.length + 13 + 10 ≤ 1024; omega)
  have hex2 := swapIterationPriceStoreSource (evm := evm) d (tickSqrtValue d.tickNext)
    (swapIterationSqrtFrame_step d hstep) (swapIterationSqrtFrame_result frame d)
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (tickSqrtValue d.tickNext) =
      tickSqrtValue d.tickNext := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) (tickSqrtValue_lt160 _)
  obtain ⟨a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩ :=
    swapIterationPriceStoreX a s d r1 hm1 hs hd hclean hq hdisj hb (by omega)
  refine ⟨?_, _, a2, k2, C2, by omega, r2, hm2, hs2, hd2, hp2, hmono1.trans hmono2⟩
  exact ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2 ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
