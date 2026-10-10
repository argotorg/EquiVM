import Benchmarks.UniswapV3.Pool.FlashCallValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashTransfersX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw p junk bal1 bal0 fee1 fee0 liquidity len start : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : FlashArgs) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 ⟨6727⟩
      (bal1 :: junk :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: a.amount1 :: a.amount0 ::
        EVM.word a.recipient.val :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hvalues : FlashCallValues locals a liquidity fee0 fee1 bal0 bal1)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : p.toNat + 2 ^ 140 ≤ 2 ^ 200) (hov : R.length + 30 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        ((flashTransition.body.drop 10).take 2) .reverted) ∨
    ∃ evm' σ' locals' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        ((flashTransition.body.drop 10).take 2)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      FlashCallValues locals' a liquidity fee0 fee1 bal0 bal1 ∧
      RD (deployedRuntime v) ee g s0 ⟨6827⟩
        (flashTransferRest bal1 bal0 fee1 fee0 liquidity len start a.amount1 a.amount0 a.recipient R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ 128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      next.toNat ≤ p.toNat + 2 ^ 139 + 326 := by
  rcases flashTransferX (v := v) false a.recipient locals rd hs hperm hvalues.core.recipient
      hvalues.core.amount0 hm hmem hzero (by omega) hov with
    ⟨rdBad, hbad⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, k1, C1, hs1, hsource0, rd1, hm1, hmem1, hz1, hp1⟩
  · exact Or.inl ⟨rdBad, ExecBlock.consRevert hbad⟩
  · have hvalues1 := hvalues.transfer false a.amount0
    rcases flashTransferX (v := v) (junk := ⟨0⟩) true a.recipient _ rd1 hs1 hperm
        hvalues1.core.recipient hvalues1.core.amount1 hm1 hmem1 hz1 (by omega) hov with
      ⟨rdBad, hbad⟩ | ⟨evm2, σ2, out2, mem2, aw2, p2, k2, C2, hs2, hsource1, rd2, hm2, hmem2, hz2, hp2⟩
    · exact Or.inl ⟨rdBad, ExecBlock.consNormal hsource0 (ExecBlock.consRevert hbad)⟩
    · exact Or.inr ⟨evm2, σ2, _, out2, mem2, aw2, p2, k2, C2, hs2,
        ExecBlock.consNormal hsource0 (ExecBlock.consNormal hsource1 ExecBlock.nil),
        hvalues1.transfer true a.amount1, rd2, hm2, hmem2, hz2, by omega⟩

end Benchmarks.UniswapV3.Pool
