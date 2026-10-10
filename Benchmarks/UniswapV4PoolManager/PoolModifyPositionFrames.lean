import Benchmarks.UniswapV4PoolManager.PoolModifyPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolModifyPositionAfterFrame (f : Frame) (evm : State) (id key : UInt256) (delta : Int)
    (fee0 fee1 : UInt256) : Frame :=
  let owed0 := positionUpdateOwed evm id key delta fee0 false
  let owed1 := positionUpdateOwed evm id key delta fee1 true
  poolModifyOwedFrame
    (resumeAfterInternalCall (poolModifyUpdateAliasFrame f id key) "__c8"
      (some [.int (Int.ofNat owed0.toNat), .int (Int.ofNat owed1.toNat)])) owed0 owed1

theorem poolModifyPositionUpdateResult_normal {f f' : Frame} {evm post : State} {id key fee0 fee1 : UInt256}
    {delta : Int} (h : poolModifyPositionUpdateResult f evm id key delta fee0 fee1 = .ok f' post) :
    f' = poolModifyPositionAfterFrame f evm id key delta fee0 fee1 ∧
    post = positionUpdatePost evm id key delta fee0 fee1 := by
  obtain ⟨cf, mid, values, hret, hn⟩ := continueCallResult_ok h
  cases hn
  exact ⟨by rw [positionUpdateReturnedValues hret]; rfl, positionUpdateReturnedState hret⟩

theorem poolModifyPositionAfterFrame_context {f : Frame} {id : UInt256} {p : PoolModifyParams}
    (hc : PoolModifyContext f id p) (evm : State) (key fee0 fee1 : UInt256) :
    PoolModifyContext (poolModifyPositionAfterFrame f evm id key p.delta fee0 fee1) id p :=
  (((hc.insert poolModifyUpdateAlias _ (by decide)).resume "__c8" _ (by decide)).insert
    "feesOwed0" _ (by decide)).insert "feesOwed1" _ (by decide)

theorem poolModifyPositionAfterFrame_get (f : Frame) (evm : State) (id key : UInt256) (delta : Int)
    (fee0 fee1 : UInt256) (name : Ident) (ha : (poolModifyUpdateAlias == name) = false)
    (hc : ("__c8" == name) = false) (h0 : ("feesOwed0" == name) = false) (h1 : ("feesOwed1" == name) = false) :
    (poolModifyPositionAfterFrame f evm id key delta fee0 fee1).locals.get? name = f.locals.get? name :=
  store_get_ne4 _ _ _ _ _ ha hc h0 h1

end Benchmarks.UniswapV4PoolManager
