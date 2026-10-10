import Benchmarks.UniswapV3.Pool.MintBeforeBalance0Trace
import Benchmarks.UniswapV3.Pool.MintBeforeBalance1Trace
import Benchmarks.UniswapV3.Pool.MintCallValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintBeforeBalancesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 key : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : MintArgs) (locals : Store) (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5915⟩
      (amount1 :: amount0 :: key :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hv : MintCallValues locals a amount0 amount1 ⟨0⟩ ⟨0⟩)
    (hm : HeapMemory mem aw p) (hsize : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintTransition.body.drop 14 |>.take 2) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ evm' σ' out mem' aw' free locals' balance0 balance1 k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintTransition.body.drop 14 |>.take 2)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      MintCallValues locals' a amount0 amount1 balance0 balance1 ∧
      RD (deployedRuntime v) ee g s0 ⟨5966⟩
        (balance1 :: balance0 :: amount1 :: amount0 :: amount1 :: amount0 :: R)
        mem' aw' out σ' k' C' ∧ HeapMemory mem' aw' free ∧ 128 ≤ mem'.size ∧
      memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧ free.toNat ≤ p.toNat + 2 ^ 139 + 262) := by
  rcases mintBeforeBalance0X (v := v) locals hs rd hv.core.amount0 hv.before0 hm hsize hzero
      (by omega) hov with ⟨hbad, rr⟩ |
      ⟨evm1, σ1, out1, mem1, aw1, p1, b0, k1, C1, hs1, hc0, r1, hm1, hmem1, hp1, hz0⟩
  · exact Or.inl ⟨ExecBlock.consRevert hbad, rr⟩
  let f1 := mintBeforeBalanceFrame v locals false amount0 b0
  have hv1 : MintCallValues f1.locals a amount0 amount1 b0 ⟨0⟩ :=
    hv.beforeBalance v false b0 hz0
  have hsize1 := le_trans hsize hmem1.size
  have hzero1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad hmem1 (UInt256.ofNat 96) (by decide) hm.lower hsize, hzero]
  rcases mintBeforeBalance1X (v := v) f1.locals hs1 r1 hv1.core.amount1 hv1.before1 hm1
      hsize1 hzero1 (by omega) hov with ⟨hbad, rr⟩ |
      ⟨evm2, σ2, out2, mem2, aw2, p2, b1, k2, C2, hs2, hc1, r2, hm2, hmem2, hp2, hz1⟩
  · exact Or.inl ⟨ExecBlock.consNormal hc0 (ExecBlock.consRevert hbad), rr⟩
  let f2 := mintBeforeBalanceFrame v f1.locals true amount1 b1
  have hv2 : MintCallValues f2.locals a amount0 amount1 b0 b1 :=
    hv1.beforeBalance v true b1 hz1
  refine Or.inr ⟨evm2, σ2, out2, mem2, aw2, p2, f2.locals, b0, b1, k2, C2, hs2,
    ExecBlock.consNormal hc0 (ExecBlock.consNormal hc1 ExecBlock.nil), hv2, r2, hm2,
    le_trans hsize1 hmem2.size, ?_, ?_⟩
  · rw [MemoryPrefix.memLoad hmem2 (UInt256.ofNat 96) (by decide) hm1.lower hsize1, hzero1]
  · omega

end Benchmarks.UniswapV3.Pool
