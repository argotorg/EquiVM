import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapResultActiveWords
import Benchmarks.UniswapV4PoolManager.PoolSwapActiveWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem poolSwapStepFillAW_active (aw : UInt256) {state params : UInt256}
    (hl : 96 ≤ state.toNat) (hb : params.toNat+160 ≤ state.toNat)
    (hf : state.toNat+352 < UInt256.size) :
    PoolSwapActiveWords (poolSwapStepFillAW aw (state+UInt256.ofNat 96))
      (state+UInt256.ofNat 96) state params := by
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  have h224 := uadd_word_ofNat_toNat (state+UInt256.ofNat 96) 224 (by rw [h96]; omega)
  have hs := memoryWords_ge_span (poolSwapStepZeroAW aw (state+UInt256.ofNat 96))
    ((state+UInt256.ofNat 96)+UInt256.ofNat 224) ⟨32⟩ (by decide)
  rw [h224, h96] at hs
  change (state.toNat+96+224+32+31)/32 ≤ _ at hs
  have he : state.toNat+352 ≤ (poolSwapStepFillAW aw (state+UInt256.ofNat 96)).toNat*32 := by
    unfold poolSwapStepFillAW
    omega
  exact ⟨by omega, by rw [h96]; omega, by omega, by omega⟩

end Benchmarks.UniswapV4PoolManager
