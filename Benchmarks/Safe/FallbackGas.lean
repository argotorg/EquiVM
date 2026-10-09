import Benchmarks.Safe.GasMemory
import Benchmarks.Safe.Blocks.Runtime_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem safeFallbackHugeOOG {I g s0 σ k C rdata}
    {handler : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨588⟩ (handler :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hsize : I.calldata.size < UInt256.size)
    (hhuge : 2 ^ 138 ≤ I.calldata.size) :
    X (g.toNat + 1) (D_J safeBytecode 0) s0 = .error .OutOfGass := by
  have hr := safeRuntime_block_588 hov h
  have hc := memExpansionCost_huge (UInt256.ofNat 3) ⟨128⟩
    (UInt256.ofNat I.calldata.size) (by decide)
    (by rwa [ulit_toNat' _ hsize])
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hm : M (UInt256.ofNat 3) (UInt256.ofNat 64) ⟨32⟩ = UInt256.ofNat 3 := rfl
  rw [hf, hm] at hr
  have hg : g.toNat < UInt256.size := g.isLt
  exact RD.oog_of_cost_gt hr (by omega)

end Benchmarks.Safe
