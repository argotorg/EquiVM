import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapGuardsTrace
import Benchmarks.UniswapV4PoolManager.MemoryActiveRange

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapResultZeroAW_covers (aw : UInt256) {state params : UInt256}
    (hf : state.toNat+96 < UInt256.size) :
    state.toNat+96 ≤ (poolSwapResultZeroAW aw state params).toNat*32 := by
  have hs := memoryWords_ge_span
    (M (M aw state ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩)
    (state+UInt256.ofNat 64) ⟨32⟩ (by decide)
  have hm := memoryWords_ge_active
    (M (M (M aw state ⟨32⟩) (state+UInt256.ofNat 32) ⟨32⟩) (state+UInt256.ofNat 64) ⟨32⟩)
    (params+UInt256.ofNat 64) ⟨32⟩
  rw [uadd_word_ofNat_toNat state 64 (by omega)] at hs
  change (state.toNat+64+32+31)/32 ≤ _ at hs
  change state.toNat+96 ≤ _
  unfold poolSwapResultZeroAW
  omega

theorem poolSwapResultInitAW_eq {aw state params : UInt256}
    (hs : state.toNat+96 ≤ aw.toNat*32) (hp : params.toNat+160 ≤ aw.toNat*32) :
    poolSwapResultInitAW aw state params = aw := by
  have hs0 : M aw state ⟨32⟩ = aw := memoryWords_eq_self (by change state.toNat+32 ≤ _; omega)
  have hp0 : M aw params ⟨32⟩ = aw := memoryWords_eq_self (by change params.toNat+32 ≤ _; omega)
  simp only [poolSwapResultInitAW, hs0, hp0,
    memoryWords_eq_self_of_range hs (by decide : 32+32 ≤ 96),
    memoryWords_eq_self_of_range hs (by decide : 64+32 ≤ 96),
    memoryWords_eq_self_of_range hp (by decide : 128+32 ≤ 160)]

theorem poolSwapLoadedAW_eq {aw state params : UInt256}
    (hf : state.toNat+96 < UInt256.size) (hb : params.toNat+160 ≤ state.toNat) :
    poolSwapLoadedAW aw state params = poolSwapResultZeroAW aw state params := by
  have hs := poolSwapResultZeroAW_covers aw hf (params := params)
  exact poolSwapResultInitAW_eq hs (by omega)

theorem poolSwapZeroAW_eq {aw params : UInt256} (fee : UInt256)
    (hp : params.toNat+160 ≤ aw.toNat*32) : poolSwapZeroAW aw fee params = aw := by
  have hp0 : M aw params ⟨32⟩ = aw := memoryWords_eq_self (by change params.toNat+32 ≤ _; omega)
  simp only [poolSwapZeroAW, poolSwapModeAW, hp0, ite_self]

theorem poolSwapGuardsAW_eq {aw params : UInt256} (fee : UInt256)
    (hp : params.toNat+160 ≤ aw.toNat*32) : poolSwapGuardsAW aw fee params = aw := by
  rw [poolSwapGuardsAW, poolSwapZeroAW_eq fee hp]
  simp only [poolSwapLimitAW, memoryWords_eq_self_of_range hp (by decide : 96+32 ≤ 160)]

end Benchmarks.UniswapV4PoolManager
