import Benchmarks.UniswapV4PoolManager.PoolModifyFeeInside
import Benchmarks.UniswapV4PoolManager.PoolModifyPositionFrames
import Benchmarks.UniswapV4PoolManager.PoolModifyFeeDelta
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFeeWord (evm : State) (id : UInt256) (p : PoolModifyParams) (second : Bool) : UInt256 :=
  poolFeeInsideWord evm id (EVM.signed p.lower) (EVM.signed p.upper) second
def poolModifyPositionOwed (evm : State) (id : UInt256) (p : PoolModifyParams) (second : Bool) : UInt256 :=
  positionUpdateOwed evm id (poolModifyPositionKey p) p.delta (poolModifyFeeWord evm id p second) second
def poolModifyFeesPreludeFrame (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : Frame :=
  poolModifyPositionGetFrame (poolModifyFeeInsideFrame f evm id p) id p
def poolModifyFeesResult (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) : ExecResult :=
  let fp := poolModifyFeesPreludeFrame f evm id p
  continueBlockResult (fun f1 post => poolModifyFeeDeltaResult f1 post
    (poolModifyPositionOwed evm id p false) (poolModifyPositionOwed evm id p true))
    (poolModifyPositionUpdateResult fp evm id (poolModifyPositionKey p) p.delta
      (poolModifyFeeWord evm id p false) (poolModifyFeeWord evm id p true))

theorem poolModifyFeesPrelude {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 8).take 7)
      (.ok (poolModifyFeesPreludeFrame f evm id p) evm) := by
  have hfee := poolModifyFeeInside (evm := evm) hc
  have hpos := poolModifyPositionGet (evm := evm) (poolModifyFeeInsideFrame_context hc evm) hl hu
  exact execBlock_append hfee hpos

theorem poolModifyFeesPreludeFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (evm : State) :
    PoolModifyContext (poolModifyFeesPreludeFrame f evm id p) id p :=
  poolModifyPositionGetFrame_context (poolModifyFeeInsideFrame_context hc evm)

theorem poolModifyFeesPreludeFrame_get (f : Frame) (evm : State) (id : UInt256) (p : PoolModifyParams) (name : Ident)
    (ha : (poolModifyFeeInsideAlias == name) = false) (h6 : ("__c6" == name) = false)
    (h0 : ("feeGrowthInside0X128" == name) = false) (h1 : ("feeGrowthInside1X128" == name) = false)
    (hp : (poolModifyPositionAlias == name) = false) (h7 : ("__c7" == name) = false)
    (hpos : ("position" == name) = false) :
    (poolModifyFeesPreludeFrame f evm id p).locals.get? name = f.locals.get? name :=
  (poolModifyPositionGetFrame_get _ _ _ name hp h7 hpos).trans
    (poolModifyFeeInsideFrame_get f evm id p name ha h6 h0 h1)

theorem poolModifyFees {f : Frame} {evm : State} {id : UInt256} {p : PoolModifyParams} {oldFee : Value}
    (hc : PoolModifyContext f id p) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hfee : f.locals.get? "feeDelta" = some oldFee) :
    ExecBlock config f evm ((poolModifyFunction.body.drop 8).take 15) (poolModifyFeesResult f evm id p) := by
  let fp := poolModifyFeesPreludeFrame f evm id p
  have hpre := poolModifyFeesPrelude (evm := evm) hc hl hu
  have hcp : PoolModifyContext fp id p := poolModifyFeesPreludeFrame_context hc evm
  have h0p : fp.locals.get? "feeGrowthInside0X128" = some (.int (Int.ofNat (poolModifyFeeWord evm id p false).toNat)) :=
    (poolModifyPositionGetFrame_get _ _ _ _ (by decide) (by decide) (by decide)).trans
      ((store_get_ne _ _ (by decide : ("feeGrowthInside1X128" == "feeGrowthInside0X128") = false)).trans (store_get_self _ _ _))
  have h1p : fp.locals.get? "feeGrowthInside1X128" = some (.int (Int.ofNat (poolModifyFeeWord evm id p true).toNat)) :=
    (poolModifyPositionGetFrame_get _ _ _ _ (by decide) (by decide) (by decide)).trans (store_get_self _ _ _)
  have hupdate := poolModifyPositionUpdate (f := fp) (evm := evm) hcp (store_get_self _ _ _) h0p h1p
  have htail : ExecBlock config fp evm ((poolModifyFunction.body.drop 15).take 8)
      (poolModifyFeesResult f evm id p) := by
    apply execBlock_continue hupdate
    intro f1 post hpost
    obtain ⟨rfl, _⟩ := poolModifyPositionUpdateResult_normal hpost
    have hc1 := poolModifyPositionAfterFrame_context hcp evm (poolModifyPositionKey p)
      (poolModifyFeeWord evm id p false) (poolModifyFeeWord evm id p true)
    apply poolModifyFeeDelta hc1.contract
    · exact (store_get_ne _ _ (by decide : ("feesOwed1" == "feesOwed0") = false)).trans (store_get_self _ _ _)
    · exact store_get_self _ _ _
    · exact (poolModifyPositionAfterFrame_get _ _ _ _ _ _ _ "feeDelta" (by decide) (by decide) (by decide) (by decide)).trans
        ((poolModifyFeesPreludeFrame_get _ _ _ _ "feeDelta" (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans hfee)
  exact execBlock_append hpre htail

end Benchmarks.UniswapV4PoolManager
