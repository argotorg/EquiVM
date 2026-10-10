import Benchmarks.UniswapV3.Pool.SwapInitialized
import Benchmarks.UniswapV3.Pool.SwapTailFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossFinishX {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (out : SwapTailExit v ee g s0 rdata ⟨3893⟩ q p cache
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      d [swapCrossBody[0]!] frame evm mem aw free C)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hd : frame.locals.get? "step" = some d.value)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23)
    (hcache : 96 ≤ cache.toNat) (hcp : cache.toNat + 192 ≤ p.toNat)
    (hpq : p.toNat + 224 ≤ q.toNat) (hbq : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    Nonempty (SwapTailExit v ee g s0 rdata ⟨3993⟩ q p cache
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      d swapCrossBody frame evm mem aw free C) := by
  have hz1 := (out.locals_get "zeroForOne" (by decide)).trans hz
  have hd1 := (out.locals_get "step" (by decide)).trans hd
  have hex := swapCrossTickSource (evm := out.evm') a.zeroForOne out.stateData d
    hz1 out.state_get hd1
  obtain ⟨m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hmono⟩ :=
    swapCrossTickX (v := v) a out.stateData d out.rd out.heap out.state_mem out.step_mem
      ht (by omega) hpq hbq hov
  have hcost := out.cost_bound
  have hcover := out.cover
  refine ⟨{
    cacheData := out.cacheData
    stateData := swapCrossTickState a.zeroForOne out.stateData d
    frame' := swapCrossTickFrame out.frame' a.zeroForOne out.stateData d
    evm' := out.evm', accounts := out.accounts
    mem := m1, aw := a1, free := out.free, k := k1, cost := C1
    source := execBlock_append_ok out.source (ExecBlock.consNormal hex .nil)
    source_state := out.source_state
    contract_eq := out.contract_eq, immutables_eq := out.immutables_eq
    cache_get := (swapStateFrame_get out.frame' _ "cache" (by decide)).trans out.cache_get
    state_get := Std.HashMap.getElem?_insert_self
    locals_get := ?_
    cache_fits := out.cache_fits
    state_fits := swapCrossTickState_fits a.zeroForOne out.stateData d out.state_fits ht
    rd := r1, heap := hm1
    cache_mem := MemoryPrefix.wordArray hp1 out.cache_mem hcache hcp
    state_mem := hs1, step_mem := hd1
    memory_prefix := out.memory_prefix.trans (hp1.mono (by omega))
    free_mono := out.free_mono, cover := by omega, cost_bound := by omega }⟩
  intro name hn
  have hns : name ≠ "state" := by
    intro h
    subst name
    exact hn (by decide)
  exact (swapStateFrame_get out.frame' _ name hns).trans (out.locals_get name hn)

end Benchmarks.UniswapV3.Pool
