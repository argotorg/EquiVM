import Benchmarks.UniswapV4PoolManager.WordStructMemory
import Benchmarks.UniswapV4PoolManager.PoolSwapValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapStepWordList (s : PoolSwapStepWords) : List UInt256 :=
  [s.priceStart, s.tickNext, UInt256.fromBool s.initialized, s.priceNext,
    s.amountIn, s.amountOut, s.feeAmount, s.feeGrowthGlobal]

def poolSwapResultWordList (r : PoolSwapResultWords) : List UInt256 :=
  [r.price, r.tick, r.liquidity]

def poolSwapParamsWordList (p : PoolSwapParamsWords) : List UInt256 :=
  [p.amountSpecified, p.tickSpacing, UInt256.fromBool p.zeroForOne, p.priceLimit, p.lpFeeOverride]

structure PoolSwapMemoryLayout (step state params : UInt256) : Prop where
  stepLow : 128 ≤ step.toNat
  stateLow : 128 ≤ state.toNat
  paramsLow : 128 ≤ params.toNat
  stepState : step.toNat+256 ≤ state.toNat ∨ state.toNat+96 ≤ step.toNat
  stepParams : step.toNat+256 ≤ params.toNat ∨ params.toNat+160 ≤ step.toNat
  stateParams : state.toNat+96 ≤ params.toNat ∨ params.toNat+160 ≤ state.toNat

structure PoolSwapMemoryView (mem : ByteArray) (step state params : UInt256)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : Prop where
  layout : PoolSwapMemoryLayout step state params
  stepFields : WordStructView mem step (poolSwapStepWordList s)
  resultFields : WordStructView mem state (poolSwapResultWordList r)
  paramsFields : WordStructView mem params (poolSwapParamsWordList p)

theorem PoolSwapMemoryView.write_step {mem : ByteArray} {step state params : UInt256}
    {s s' : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (h : PoolSwapMemoryView mem step state params s r p) (i : Nat) (hi : i < 8) (word : UInt256)
    (he : poolSwapStepWordList s' = (poolSwapStepWordList s).set i word) :
    PoolSwapMemoryView (writeWord mem (step+UInt256.ofNat (32*i)).toNat word) step state params s' r p := by
  have hf : step.toNat+256 < UInt256.size := h.stepFields.noWrap
  have hn := uadd_word_ofNat_toNat step (32*i) (by omega)
  refine ⟨h.layout, ?_, ?_, ?_⟩
  · rw [he]; exact h.stepFields.write_field i hi word
  · apply h.resultFields.write_disjoint
    change state.toNat+96 ≤ _ ∨ _+32 ≤ state.toNat
    rw [hn]; have := h.layout.stepState; omega
  · apply h.paramsFields.write_disjoint
    change params.toNat+160 ≤ _ ∨ _+32 ≤ params.toNat
    rw [hn]; have := h.layout.stepParams; omega

theorem PoolSwapMemoryView.write_result {mem : ByteArray} {step state params : UInt256}
    {s : PoolSwapStepWords} {r r' : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (h : PoolSwapMemoryView mem step state params s r p) (i : Nat) (hi : i < 3) (word : UInt256)
    (he : poolSwapResultWordList r' = (poolSwapResultWordList r).set i word) :
    PoolSwapMemoryView (writeWord mem (state+UInt256.ofNat (32*i)).toNat word) step state params s r' p := by
  have hf : state.toNat+96 < UInt256.size := h.resultFields.noWrap
  have hn := uadd_word_ofNat_toNat state (32*i) (by omega)
  refine ⟨h.layout, ?_, ?_, ?_⟩
  · apply h.stepFields.write_disjoint
    change step.toNat+256 ≤ _ ∨ _+32 ≤ step.toNat
    rw [hn]; have := h.layout.stepState; omega
  · rw [he]; exact h.resultFields.write_field i hi word
  · apply h.paramsFields.write_disjoint
    change params.toNat+160 ≤ _ ∨ _+32 ≤ params.toNat
    rw [hn]; have := h.layout.stateParams; omega

theorem PoolSwapMemoryView.hash_scratch {mem : ByteArray} {step state params : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (h : PoolSwapMemoryView mem step state params s r p) (key base : UInt256) :
    PoolSwapMemoryView (twoWordHashMem key base mem) step state params s r p :=
  ⟨h.layout, h.stepFields.hash_scratch key base (by have := h.layout.stepLow; omega),
    h.resultFields.hash_scratch key base (by have := h.layout.stateLow; omega),
    h.paramsFields.hash_scratch key base (by have := h.layout.paramsLow; omega)⟩

end Benchmarks.UniswapV4PoolManager
