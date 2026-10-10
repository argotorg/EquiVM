import Benchmarks.UniswapV3.Pool.SwapIterationClampTrace
import Benchmarks.UniswapV3.Pool.SwapIterationTickLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationTickFrame (frame : Frame) (d : SwapIterationData) (tick : Int)
    (hit : Bool) : Frame :=
  swapIterationClampFrame (swapIterationBitmapStoresFrame frame d tick hit)
    {d with tickNext := tick, initialized := hit}

def swapIterationTickData (d : SwapIterationData) (tick : Int) (hit : Bool) : SwapIterationData :=
  {d with tickNext := swapIterationClampTick tick, initialized := hit}

theorem swapIterationTickX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free tickRaw hitRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (frame : Frame) (evm : EVM.State) (d : SwapIterationData) (tick : Int) (hit : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3109⟩ (hitRaw :: tickRaw :: p :: R)
      mem aw rdata σ k C)
    (hstep : frame.locals.get? "step" = some d.value)
    (hresult : frame.locals.get? "__c2" = some (.tuple [.int tick, .bool hit]))
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem p d)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hh : UInt256.isZero (UInt256.isZero hitRaw) = hit.toUInt256)
    (htb : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hp : 96 ≤ p.toNat) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    ExecBlock config frame evm ((swapLoopBody.drop 3).take 3)
      (.ok (swapIterationTickFrame frame d tick hit) evm) ∧
    ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3189⟩ (p :: R) mem' aw' rdata σ k' C' ∧
      HeapMemory mem' aw' free ∧ SwapIterationMemory mem' p (swapIterationTickData d tick hit) ∧
      MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  constructor
  · have hbody : (swapLoopBody.drop 3).take 3 =
        (swapLoopBody.drop 3).take 2 ++ [swapLoopBody[5]!] := rfl
    rw [hbody]
    apply execBlock_append_ok (swapIterationBitmapStoresSource d tick hit hstep hresult)
    exact ExecBlock.consNormal
      (swapIterationClampSource _ (swapIterationBitmapStoresFrame_step frame d tick hit))
      ExecBlock.nil
  · obtain ⟨a1, k1, C1, hC1, r1, hm1, hd1, hpre1, hmono1⟩ :=
      swapIterationBitmapStoreX d tick hit rd hm hd ht hh htb hp hb hov
    obtain ⟨a2, k2, C2, hC2, r2, hm2, hd2, hpre2, hmono2⟩ :=
      swapIterationClampX _ r1 hm1 hd1 htb hp hb (by omega)
    exact ⟨_, a2, k2, C2, by omega, r2, hm2, hd2, hpre1.trans hpre2, hmono1.trans hmono2⟩

theorem swapIterationTickFrame_step (frame : Frame) (d : SwapIterationData)
    (tick : Int) (hit : Bool) :
    (swapIterationTickFrame frame d tick hit).locals.get? "step" =
      some (swapIterationTickData d tick hit).value :=
  swapIterationClampFrame_step _ (swapIterationBitmapStoresFrame_step frame d tick hit)

theorem swapIterationTickData_bounds (d : SwapIterationData) (tick : Int) (hit : Bool) :
    -887272 ≤ (swapIterationTickData d tick hit).tickNext ∧
      (swapIterationTickData d tick hit).tickNext ≤ 887272 :=
  swapIterationClampTick_bounds tick

end Benchmarks.UniswapV3.Pool
