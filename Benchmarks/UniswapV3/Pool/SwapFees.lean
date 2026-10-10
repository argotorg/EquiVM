import Benchmarks.UniswapV3.Pool.SwapFeeGrowth
import Benchmarks.UniswapV3.Pool.SwapProtocolTrace
import Benchmarks.UniswapV3.Pool.SwapProtocolFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapFeesState (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData) : SwapStateData :=
  swapFeeGrowthState (swapProtocolState c s d) (swapProtocolData c d)

def swapFeesFrame (frame : Frame) (c : SwapCacheData) (s : SwapStateData)
    (d : SwapIterationData) : Frame :=
  swapFeeGrowthFrame (swapProtocolFrame frame c s d) (swapProtocolState c s d)
    (swapProtocolData c d)

theorem swapFeesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q cache exactWord free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3504⟩ ([q, p, exactWord, cache] ++ R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hcache : frame.locals.get? "cache" = some c.value)
    (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hfit : s.Fits) (hfee : c.feeProtocol.toNat < 256) (hp : 96 ≤ p.toNat)
    (hcachep : cache.toNat + 192 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 20 ≤ 1024) :
    (ExecBlock config frame evm ((swapLoopBody.drop 14).take 2) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm ((swapLoopBody.drop 14).take 2)
        (.ok (swapFeesFrame frame c s d) evm) ∧
      (swapFeesState c s d).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3637⟩ ([q, p, exactWord, cache] ++ R)
          mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' free ∧ SwapStateMemory mem' p (swapFeesState c s d) ∧
        SwapIterationMemory mem' q (swapProtocolData c d) ∧ MemoryPrefix mem mem' p.toNat ∧
        aw.toNat ≤ aw'.toNat) := by
  have hex1 := swapProtocolSource (evm := evm) c s d hcache hstate hstep
  have hfit1 := swapProtocolState_fits c s d hfit
  obtain ⟨m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hmono1⟩ :=
    swapProtocolX (v := v) c s d rd hm hc hs hd hfee hp hcachep hdisj hb (by omega)
  rcases swapFeeGrowthX (v := v) (swapProtocolState c s d) (swapProtocolData c d)
      (swapProtocolFrame frame c s d) evm r1 ((swapProtocolFrame_parts frame c s d).1.trans hf)
      (swapProtocolFrame_state c s d hstate) (swapProtocolFrame_step c s d hstep)
      hm1 hs1 hd1 hfit1 hp hdisj hb (by change R.length + 2 + 18 ≤ 1024; omega) with
    ⟨hex2, hr⟩ | ⟨hex2, m2, a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩
  · exact Or.inl ⟨ExecBlock.consNormal hex1 (ExecBlock.consRevert hex2), hr⟩
  · exact Or.inr ⟨ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2 .nil),
      swapFeeGrowthState_fits _ _ hfit1, m2, a2, k2, C2, by omega,
      r2, hm2, hs2, hd2, hp1.trans hp2, hmono1.trans hmono2⟩

end Benchmarks.UniswapV3.Pool
