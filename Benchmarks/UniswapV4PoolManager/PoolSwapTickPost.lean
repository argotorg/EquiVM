import Benchmarks.UniswapV4PoolManager.PoolSwapTickFrame
import Benchmarks.UniswapV4PoolManager.TickPriceCanonical

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapTickResult_frames {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (h : poolSwapTickResult f evm id s r zeroForOne = .ok ff post) :
    PoolSwapTickFramePost f ff evm post (poolSwapTickResultWords evm id s r zeroForOne) := by
  unfold poolSwapTickResult at h
  by_cases he : r.price = s.priceNext
  · rw [if_pos he] at h
    by_cases hi : s.initialized = true
    · rw [if_pos hi] at h
      split at h
      · cases h
      · split at h
        · cases h
          simp only [poolSwapTickResultWords, if_pos he, if_pos hi]
          exact poolSwapCrossFrame_post f evm id s r zeroForOne
        · cases h
    · rw [if_neg hi] at h
      cases h
      simp only [poolSwapTickResultWords, if_pos he, if_neg hi]
      exact poolSwapBoundaryFrame_post f evm r _
  · rw [if_neg he] at h
    unfold poolSwapRepriceResult at h
    by_cases hs : r.price = s.priceStart
    · rw [if_pos hs] at h
      cases h
      simpa only [poolSwapTickResultWords, if_neg he, if_pos hs] using poolSwapUnchangedFrame_post evm hr
    · rw [if_neg hs] at h
      cases ht : tickPriceResult r.price with
      | none => rw [ht] at h; cases h
      | some tick =>
        rw [ht] at h
        cases h
        simp only [poolSwapTickResultWords, if_neg he, if_neg hs, ht]
        exact poolSwapRepriceFrame_post f evm r tick

theorem poolSwapTickResult_canonical {f ff : Frame} {evm post : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (ht : int24Canonical r.tick) (hn : int24Canonical s.tickNext) (hl : r.liquidity.toNat < 2^128)
    (h : poolSwapTickResult f evm id s r zeroForOne = .ok ff post) :
    let r' := poolSwapTickResultWords evm id s r zeroForOne
    r'.price = r.price ∧ int24Canonical r'.tick ∧ r'.liquidity.toNat < 2^128 := by
  dsimp only
  unfold poolSwapTickResult at h
  unfold poolSwapTickResultWords
  by_cases he : r.price = s.priceNext
  · rw [if_pos he] at h ⊢
    have hbound : int24Canonical (poolSwapBoundaryTick zeroForOne s.tickNext) := by
      unfold poolSwapBoundaryTick
      split
      · exact signextend24_canonical _
      · exact hn
    by_cases hi : s.initialized = true
    · rw [if_pos hi] at h ⊢
      split at h
      · cases h
      · split at h
        · rename_i hfit
          exact ⟨rfl, hbound, liquidityAddResultWord_bound hfit⟩
        · cases h
    · rw [if_neg hi] at h ⊢
      exact ⟨rfl, hbound, hl⟩
  · rw [if_neg he] at h ⊢
    unfold poolSwapRepriceResult at h
    by_cases hs : r.price = s.priceStart
    · rw [if_pos hs]
      exact ⟨rfl, ht, hl⟩
    · rw [if_neg hs] at h ⊢
      cases htick : tickPriceResult r.price with
      | none => rw [htick] at h; cases h
      | some tick => exact ⟨rfl, tickPriceResult_canonical htick, hl⟩

end Benchmarks.UniswapV4PoolManager
