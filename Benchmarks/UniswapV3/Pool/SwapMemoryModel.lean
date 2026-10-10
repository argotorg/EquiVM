import Benchmarks.UniswapV3.Pool.SwapStateSource
import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def SwapStateData.Fits (s : SwapStateData) : Prop :=
  (-(2 ^ 255 : Int) ≤ s.remaining ∧ s.remaining < 2 ^ 255) ∧
  (-(2 ^ 255 : Int) ≤ s.calculated ∧ s.calculated < 2 ^ 255) ∧
  s.price.toNat < 2 ^ 160 ∧ (-(2 ^ 23 : Int) ≤ s.tick ∧ s.tick < 2 ^ 23) ∧
  s.protocolFee.toNat < 2 ^ 128 ∧ s.liquidity.toNat < 2 ^ 128

def SwapCacheData.Fits (c : SwapCacheData) : Prop :=
  c.feeProtocol.toNat < 16 ∧ c.liquidityStart.toNat < 2 ^ 128 ∧
  c.blockTimestamp.toNat < 2 ^ 32 ∧
  (-(2 ^ 55 : Int) ≤ c.tickCumulative ∧ c.tickCumulative < 2 ^ 55) ∧
  c.secondsPerLiquidity.toNat < 2 ^ 160

def SwapStateMemory (mem : ByteArray) (p : UInt256) (s : SwapStateData) : Prop :=
  WordArrayMemory mem p s.words

def SwapCacheMemory (mem : ByteArray) (p : UInt256) (c : SwapCacheData) : Prop :=
  WordArrayMemory mem p c.words

theorem swapCacheInitial_fits (a : SwapArgs) (evm : EVM.State) :
    (swapCacheInitial a evm).Fits := by
  dsimp only [SwapCacheData.Fits, swapCacheInitial]
  exact ⟨poolProtocolDivisor_lt _ _ _, poolLiquidityWord_lt _ _, blockTimestampWord_lt _,
    ⟨by decide, by decide⟩, by decide⟩

theorem swapStateInitial_fits (a : SwapArgs) (evm : EVM.State) (ha : a.Fits) :
    (swapStateInitial a evm).Fits := by
  dsimp only [SwapStateData.Fits, swapStateInitial]
  refine ⟨ha.1, ⟨by decide, by decide⟩, ?_, ?_, by decide, poolLiquidityWord_lt _ _⟩
  · exact u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)
  · exact normalizeSint_bounds ⟨24, by decide⟩ _

theorem swapExactInput_word (a : SwapArgs) (ha : a.Fits) :
    UInt256.sgt (EVM.wordOfInt a.amountSpecified) (UInt256.ofNat 0) =
      (swapExactInput a).toUInt256 := by
  rw [sgt_eq_slt_swap]
  have h0 : UInt256.ofNat 0 = EVM.wordOfInt 0 := rfl
  rw [h0, slt_wordOfInt 0 a.amountSpecified (by decide) (by decide) ha.1.1 ha.1.2]
  by_cases h : 0 < a.amountSpecified <;> simp only [swapExactInput, h, ↓reduceIte,
    decide_true, decide_false] <;> rfl

theorem SwapStateMemory.load_remaining {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad p mem = EVM.wordOfInt s.remaining := by
  have h := WordArrayMemory.load hm 0 (by change 0 < 7; decide) hb
  have h0 : p + UInt256.ofNat 0 = p := u256_add_zero p
  simpa only [SwapStateData.words, List.getElem_cons_zero, Nat.mul_zero, h0] using h

theorem SwapStateMemory.load_price {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 64) mem = s.price := by
  have h := WordArrayMemory.load hm 2 (by change 2 < 7; decide) hb
  simpa only [SwapStateData.words, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul] using h

end Benchmarks.UniswapV3.Pool
