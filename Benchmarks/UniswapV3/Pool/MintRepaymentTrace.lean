import Benchmarks.UniswapV3.Pool.MintRepaySideTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintRepaymentX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw p before0 before1 amount0 amount1 junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : MintArgs) (locals : Store) (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨6116⟩
      (junk0 :: junk1 :: junk2 :: junk3 :: mintRepayWords before0 before1 amount0 amount1 R)
      mem aw rdata σ k C) (hv : MintCallValues locals a amount0 amount1 before0 before1)
    (hm : HeapMemory mem aw p) (hsize : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    (ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintTransition.body.drop 19 |>.take 2) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ evm' σ' out mem' aw' free locals' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (mintTransition.body.drop 19 |>.take 2)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      MintCallValues locals' a amount0 amount1 before0 before1 ∧
      RD (deployedRuntime v) ee g s0 ⟨6283⟩
        (mintRepayWords before0 before1 amount0 amount1 R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' free ∧ free.toNat ≤ p.toNat + 2 ^ 139 + 262) := by
  rcases mintRepaySideX (v := v) false a locals hs rd hv hm hsize hzero (by omega) hov with
    ⟨hbad, rr⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, locals1, k1, C1,
      hs1, hc0, hv1, r1, hm1, hsize1, hzero1, hp1⟩
  · exact Or.inl ⟨ExecBlock.consRevert hbad, rr⟩
  rcases mintRepaySideX (v := v) (junk0 := ⟨0⟩) (junk1 := ⟨0⟩)
      (junk2 := ⟨0⟩) (junk3 := ⟨0⟩) true a locals1 hs1 r1 hv1 hm1 hsize1 hzero1
      (by omega) hov with ⟨hbad, rr⟩ |
      ⟨evm2, σ2, out2, mem2, aw2, p2, locals2, k2, C2,
        hs2, hc1, hv2, r2, hm2, _, _, hp2⟩
  · exact Or.inl ⟨ExecBlock.consNormal hc0 (ExecBlock.consRevert hbad), rr⟩
  exact Or.inr ⟨evm2, σ2, out2, mem2, aw2, p2, locals2, k2, C2, hs2,
    ExecBlock.consNormal hc0 (ExecBlock.consNormal hc1 ExecBlock.nil), hv2, r2, hm2, by omega⟩

end Benchmarks.UniswapV3.Pool
