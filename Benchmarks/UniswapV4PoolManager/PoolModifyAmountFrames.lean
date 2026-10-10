import Benchmarks.UniswapV4PoolManager.PoolModifyAmounts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyOutsideDeltaWord (one : Bool) (p : PoolModifyParams) : UInt256 :=
  balanceDeltaWord (if one then ⟨0⟩ else poolModifyOutsideWord one p) (if one then poolModifyOutsideWord one p else ⟨0⟩)
def poolModifyOutsideFrame (f : Frame) (one : Bool) (p : PoolModifyParams) : Frame :=
  balanceDeltaAssignFrame
    (checkedSignedAmountFrame (poolModifyOutsidePricesFrame f one p) (poolModifyOutsideAmountRet one)
      (poolModifyOutsideCastRet one) (poolModifyOutsideWord one p)) (poolModifyOutsidePackRet one) "delta"
    (if one then ⟨0⟩ else poolModifyOutsideWord one p) (if one then poolModifyOutsideWord one p else ⟨0⟩)

theorem poolModifyOutsideResult_normal {f f' : Frame} {evm post : State} {one : Bool} {p : PoolModifyParams}
    (h : poolModifyOutsideResult f evm one p = .ok f' post) : f' = poolModifyOutsideFrame f one p ∧ post = evm := by
  obtain ⟨f1, mid, hc, hn⟩ := continueBlockResult_ok h
  obtain ⟨rfl, hm⟩ := checkedSignedAmountResult_normal hc
  subst mid
  cases hn
  exact ⟨rfl, rfl⟩

theorem poolModifyOutsideResult_delta {f f' : Frame} {evm post : State} {one : Bool} {p : PoolModifyParams}
    (h : poolModifyOutsideResult f evm one p = .ok f' post) :
    f'.locals.get? "delta" = some (.int (EVM.signed (poolModifyOutsideDeltaWord one p))) := by
  rw [(poolModifyOutsideResult_normal h).1]
  exact store_get_self _ _ _

theorem poolModifyOutsideResult_fee {f f' : Frame} {evm post : State} {one : Bool} {p : PoolModifyParams}
    (h : poolModifyOutsideResult f evm one p = .ok f' post) : f'.locals.get? "feeDelta" = f.locals.get? "feeDelta" := by
  rw [(poolModifyOutsideResult_normal h).1]
  exact (store_get_ne2 _ _ _
    (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsidePackRet one == "feeDelta") = false)
    (by decide : ("delta" == "feeDelta") = false)).trans
    (store_get_ne4 _ _ _ _ _
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideLowerRet one == "feeDelta") = false)
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideUpperRet one == "feeDelta") = false)
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideAmountRet one == "feeDelta") = false)
      (by exact Bool.rec (by decide) (by decide) one : (poolModifyOutsideCastRet one == "feeDelta") = false))

def poolModifyInsideDeltaWord (p : PoolModifyParams) (sqrtPrice : UInt256) : UInt256 :=
  balanceDeltaWord (poolModifyRegionWord false p sqrtPrice) (poolModifyRegionWord true p sqrtPrice)
def poolModifyInsideFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) (sqrtPrice : UInt256) : Frame :=
  let f1 := poolModifyRegionAmountFrame f false p sqrtPrice
  let f2 := poolModifyRegionAmountFrame f1 true p sqrtPrice
  wordLocal (poolModifyInsidePackFrame f2 p sqrtPrice) "__c28" (liquidityAddResultWord (poolLiquidityWord evm id) p.delta)

theorem poolModifyInsideResult_normal {f f' : Frame} {evm post : State} {id sqrtPrice : UInt256} {p : PoolModifyParams}
    (h : poolModifyInsideResult f evm id p sqrtPrice = .ok f' post) :
    f' = poolModifyInsideFrame f evm id p sqrtPrice ∧
    post = poolLiquidityStore evm id (liquidityAddResultWord (poolLiquidityWord evm id) p.delta) := by
  obtain ⟨f1, mid1, h0, hn⟩ := continueBlockResult_ok h
  obtain ⟨rfl, hm1⟩ := poolModifyRegionAmountResult_normal h0
  subst mid1
  obtain ⟨f2, mid2, h1, hdone⟩ := continueBlockResult_ok hn
  obtain ⟨rfl, hm2⟩ := poolModifyRegionAmountResult_normal h1
  subst mid2
  exact poolModifyLiquidityResult_normal hdone

theorem poolModifyInsideResult_delta {f f' : Frame} {evm post : State} {id sqrtPrice : UInt256} {p : PoolModifyParams}
    (h : poolModifyInsideResult f evm id p sqrtPrice = .ok f' post) :
    f'.locals.get? "delta" = some (.int (EVM.signed (poolModifyInsideDeltaWord p sqrtPrice))) := by
  rw [(poolModifyInsideResult_normal h).1]
  exact (store_get_ne _ _ (by decide : ("__c28" == "delta") = false)).trans (store_get_self _ _ _)

theorem poolModifyInsideResult_fee {f f' : Frame} {evm post : State} {id sqrtPrice : UInt256} {p : PoolModifyParams}
    (h : poolModifyInsideResult f evm id p sqrtPrice = .ok f' post) : f'.locals.get? "feeDelta" = f.locals.get? "feeDelta" := by
  rw [(poolModifyInsideResult_normal h).1]
  exact (store_get_ne3 _ _ _ _ (by decide : ("__c27" == "feeDelta") = false)
    (by decide : ("delta" == "feeDelta") = false) (by decide : ("__c28" == "feeDelta") = false)).trans
    ((poolModifyRegionAmountFrame_get _ true _ _ "feeDelta" (by decide) (by decide) (by decide)).trans
      (poolModifyRegionAmountFrame_get _ false _ _ "feeDelta" (by decide) (by decide) (by decide)))

end Benchmarks.UniswapV4PoolManager
