import Benchmarks.UniswapV4PoolManager.PoolModifyPrelude
import Benchmarks.UniswapV4PoolManager.PoolModifyContext

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyPreludeFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolModifyParamsValue p)) :
    PoolModifyContext (poolModifyPreludeFrame f p) id p := by
  have hc : PoolModifyContext (poolModifyInputsFrame f p) id p := by
    constructor
    · dsimp only [poolModifyInputsFrame]
      exact hf
    · exact (store_get_ne5 _ _ _ _ _ _ (by decide : ("delta" == "self") = false)
        (by decide : ("feeDelta" == "self") = false) (by decide : ("liquidityDelta" == "self") = false)
        (by decide : ("tickLower" == "self") = false) (by decide : ("tickUpper" == "self") = false)).trans hs
    · exact (store_get_ne5 _ _ _ _ _ _ (by decide : ("delta" == "params") = false)
        (by decide : ("feeDelta" == "params") = false) (by decide : ("liquidityDelta" == "params") = false)
        (by decide : ("tickLower" == "params") = false) (by decide : ("tickUpper" == "params") = false)).trans hp
    · exact (store_get_ne _ _ (by decide : ("tickUpper" == "tickLower") = false)).trans (store_get_self _ _ _)
    · exact store_get_self _ _ _
    · exact (store_get_ne2 _ _ _ (by decide : ("tickLower" == "liquidityDelta") = false)
        (by decide : ("tickUpper" == "liquidityDelta") = false)).trans (store_get_self _ _ _)
  have hr := hc.insert "__c0" .unit (by decide)
  have ht := hr.insert "state" (poolModifyStateValue false ⟨0⟩ false ⟨0⟩) (by decide)
  simpa only [poolModifyPreludeFrame] using ht

theorem poolModifyPreludeFrame_delta (f : Frame) (p : PoolModifyParams) :
    (poolModifyPreludeFrame f p).locals.get? "delta" = some (.int 0) :=
  (store_get_ne2 _ _ _ (by decide : ("__c0" == "delta") = false) (by decide : ("state" == "delta") = false)).trans
    ((store_get_ne4 _ _ _ _ _ (by decide : ("feeDelta" == "delta") = false)
      (by decide : ("liquidityDelta" == "delta") = false) (by decide : ("tickLower" == "delta") = false)
      (by decide : ("tickUpper" == "delta") = false)).trans (store_get_self _ _ _))

theorem poolModifyPreludeFrame_fee (f : Frame) (p : PoolModifyParams) :
    (poolModifyPreludeFrame f p).locals.get? "feeDelta" = some (.int 0) :=
  (store_get_ne2 _ _ _ (by decide : ("__c0" == "feeDelta") = false) (by decide : ("state" == "feeDelta") = false)).trans
    ((store_get_ne3 _ _ _ _ (by decide : ("liquidityDelta" == "feeDelta") = false)
      (by decide : ("tickLower" == "feeDelta") = false) (by decide : ("tickUpper" == "feeDelta") = false)).trans
        (store_get_self _ _ _))

end Benchmarks.UniswapV4PoolManager
