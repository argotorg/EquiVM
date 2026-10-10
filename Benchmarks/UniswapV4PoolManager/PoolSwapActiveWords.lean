import Benchmarks.UniswapV4PoolManager.MemoryActiveRange
import Benchmarks.UniswapV4PoolManager.PoolSwapScanComputeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolSwapActiveWords (aw step state params : UInt256) : Prop where
  scratch : 96 ≤ aw.toNat*32
  step : step.toNat+256 ≤ aw.toNat*32
  state : state.toNat+96 ≤ aw.toNat*32
  params : params.toNat+160 ≤ aw.toNat*32

namespace PoolSwapActiveWords

variable {aw step state params : UInt256} (h : PoolSwapActiveWords aw step state params)
include h

theorem step_word {n : Nat} (hn : n+32 ≤ 256) : M aw (step+UInt256.ofNat n) ⟨32⟩ = aw :=
  memoryWords_eq_self_of_range h.step hn
theorem state_word {n : Nat} (hn : n+32 ≤ 96) : M aw (state+UInt256.ofNat n) ⟨32⟩ = aw :=
  memoryWords_eq_self_of_range h.state hn
theorem params_word {n : Nat} (hn : n+32 ≤ 160) : M aw (params+UInt256.ofNat n) ⟨32⟩ = aw :=
  memoryWords_eq_self_of_range h.params hn
theorem step_base : M aw step ⟨32⟩ = aw := memoryWords_eq_self (by have := h.step; change step.toNat+32 ≤ _; omega)
theorem state_base : M aw state ⟨32⟩ = aw := memoryWords_eq_self (by have := h.state; change state.toNat+32 ≤ _; omega)
theorem params_base : M aw params ⟨32⟩ = aw := memoryWords_eq_self (by have := h.params; change params.toNat+32 ≤ _; omega)
theorem scratch_access {off len : UInt256} (hb : off.toNat+len.toNat ≤ 96) : M aw off len = aw :=
  memoryWords_eq_self (hb.trans h.scratch)

theorem scan : poolSwapScanAW aw step state params = aw := by
  simp only [poolSwapScanAW, poolSwapScanStartAW, h.state_base, h.step_base,
    h.state_word (by decide : 32+32 ≤ 96), h.params_word (by decide : 32+32 ≤ 160),
    h.scratch_access (by decide : (⟨0⟩ : UInt256).toNat+(⟨32⟩ : UInt256).toNat ≤ 96),
    h.scratch_access (by decide : (UInt256.ofNat 32).toNat+(⟨32⟩ : UInt256).toNat ≤ 96),
    h.scratch_access (by decide : (⟨0⟩ : UInt256).toNat+(UInt256.ofNat 64).toNat ≤ 96),
    h.step_word (by decide : 64+32 ≤ 256), h.step_word (by decide : 32+32 ≤ 256)]

theorem compute : poolSwapComputeAW aw step state params = aw := by
  change poolSwapComputeStoreAW
    (swapStepStartAW aw step (UInt256.ofNat 96) state params (UInt256.ofNat 64)) step state params = aw
  simp only [poolSwapComputeAW, swapStepStartAW, poolSwapComputeStoreAW,
    h.step_word (by decide : 96+32 ≤ 256), h.state_base,
    h.params_word (by decide : 96+32 ≤ 160), h.state_word (by decide : 64+32 ≤ 96),
    h.step_word (by decide : 192+32 ≤ 256), h.step_word (by decide : 160+32 ≤ 256),
    h.step_word (by decide : 128+32 ≤ 256), h.params_base]

theorem scan_compute : poolSwapScanComputeAW aw step state params = aw := by
  rw [poolSwapScanComputeAW, h.scan, h.compute]


theorem accounting (specified fee protocol : UInt256) (s : PoolSwapStepWords) (r : PoolSwapResultWords) :
    poolSwapAccountingAW aw step state specified s r fee protocol = aw := by
  unfold poolSwapAccountingAW poolSwapAmountAW poolSwapProtocolAW poolSwapProtocolActiveAW
    poolSwapGrowthAW poolSwapTickAW poolSwapTickBranchAW poolSwapCrossAW
  simp only [h.step_base, h.state_base,
    h.step_word (by decide : 32+32 ≤ 256), h.step_word (by decide : 64+32 ≤ 256),
    h.step_word (by decide : 96+32 ≤ 256), h.step_word (by decide : 128+32 ≤ 256),
    h.step_word (by decide : 160+32 ≤ 256), h.step_word (by decide : 192+32 ≤ 256),
    h.step_word (by decide : 224+32 ≤ 256), h.state_word (by decide : 32+32 ≤ 96),
    h.state_word (by decide : 64+32 ≤ 96),
    h.scratch_access (by decide : (⟨0⟩ : UInt256).toNat+(⟨32⟩ : UInt256).toNat ≤ 96),
    h.scratch_access (by decide : (UInt256.ofNat 32).toNat+(⟨32⟩ : UInt256).toNat ≤ 96),
    h.scratch_access (by decide : (⟨0⟩ : UInt256).toNat+(UInt256.ofNat 64).toNat ≤ 96),
    ite_self]

theorem finish (p : PoolSwapParamsWords) : poolSwapFinishAW aw state step params p = aw := by
  unfold poolSwapFinishAW poolSwapStoreAW poolSwapSlot0AW poolSwapDeltaAW
  simp only [h.state_base, h.state_word (by decide : 32+32 ≤ 96),
    h.state_word (by decide : 64+32 ≤ 96), h.step_word (by decide : 224+32 ≤ 256),
    h.params_base, ite_self]

end PoolSwapActiveWords
end Benchmarks.UniswapV4PoolManager
