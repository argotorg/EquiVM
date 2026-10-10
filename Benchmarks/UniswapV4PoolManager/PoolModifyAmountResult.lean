import Benchmarks.UniswapV4PoolManager.PoolModifyAmountFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyRegionDeltaWord (p : PoolModifyParams) (tick : Int) (sqrtPrice : UInt256) : UInt256 :=
  if tick < EVM.signed p.lower then poolModifyOutsideDeltaWord false p else
    if tick < EVM.signed p.upper then poolModifyInsideDeltaWord p sqrtPrice else poolModifyOutsideDeltaWord true p
def poolModifyAmountsDeltaWord (evm : State) (id : UInt256) (p : PoolModifyParams) : UInt256 :=
  if p.delta ≠ 0 then poolModifyRegionDeltaWord p (poolCurrentTick evm id) (poolSqrtPriceWord evm id) else ⟨0⟩

theorem poolModifyRegionResult_delta {f f' : Frame} {evm post : State} {id sqrtPrice : UInt256}
    {p : PoolModifyParams} {tick : Int} (h : poolModifyRegionResult f evm id p tick sqrtPrice = .ok f' post) :
    f'.locals.get? "delta" = some (.int (EVM.signed (poolModifyRegionDeltaWord p tick sqrtPrice))) := by
  by_cases hl : tick < EVM.signed p.lower
  · rw [poolModifyRegionResult, if_pos hl] at h
    rw [poolModifyRegionDeltaWord, if_pos hl]
    exact poolModifyOutsideResult_delta h
  · rw [poolModifyRegionResult, if_neg hl] at h
    rw [poolModifyRegionDeltaWord, if_neg hl]
    by_cases hu : tick < EVM.signed p.upper
    · rw [if_pos hu] at h ⊢
      exact poolModifyInsideResult_delta h
    · rw [if_neg hu] at h ⊢
      exact poolModifyOutsideResult_delta h

theorem poolModifyRegionResult_fee {f f' : Frame} {evm post : State} {id sqrtPrice : UInt256}
    {p : PoolModifyParams} {tick : Int} (h : poolModifyRegionResult f evm id p tick sqrtPrice = .ok f' post) :
    f'.locals.get? "feeDelta" = f.locals.get? "feeDelta" := by
  unfold poolModifyRegionResult at h
  split at h
  · exact poolModifyOutsideResult_fee h
  · split at h
    · exact poolModifyInsideResult_fee h
    · exact poolModifyOutsideResult_fee h

theorem poolModifyAmountsResult_delta {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (hd : f.locals.get? "delta" = some (.int 0))
    (h : poolModifyAmountsResult f evm id p = .ok f' post) :
    f'.locals.get? "delta" = some (.int (EVM.signed (poolModifyAmountsDeltaWord evm id p))) := by
  unfold poolModifyAmountsResult at h
  split_ifs at h with hz
  · rw [poolModifyAmountsDeltaWord, if_pos hz]
    exact poolModifyRegionResult_delta h
  · cases h
    rw [poolModifyAmountsDeltaWord, if_neg hz]
    exact hd

theorem poolModifyAmountsResult_fee {f f' : Frame} {evm post : State} {id : UInt256} {p : PoolModifyParams}
    (h : poolModifyAmountsResult f evm id p = .ok f' post) :
    f'.locals.get? "feeDelta" = f.locals.get? "feeDelta" := by
  unfold poolModifyAmountsResult at h
  split_ifs at h
  · exact (poolModifyRegionResult_fee h).trans (poolModifyPricePreludeFrame_get _ _ _ "feeDelta"
      (by decide) (by decide) (by decide) (by decide) (by decide))
  · cases h
    rfl

end Benchmarks.UniswapV4PoolManager
