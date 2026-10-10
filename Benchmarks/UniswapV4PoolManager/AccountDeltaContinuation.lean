import Benchmarks.UniswapV4PoolManager.AccountDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem accountDeltaCallResult_normal {f f' : Frame} {evm post : State}
    {target currency : AccountAddress} {delta : Int} {ret : Ident}
    (h : accountDeltaCallResult f evm target currency delta ret = .ok f' post) :
    f' = {f with locals := f.locals.insert ret .unit} ∧
      post = accountDeltaPost evm target currency delta := by
  unfold accountDeltaCallResult at h
  split_ifs at h with hz hf hp
  · cases h
    exact ⟨rfl, by simp only [accountDeltaPost, if_pos hz]⟩
  · cases h
    exact ⟨rfl, rfl⟩

end Benchmarks.UniswapV4PoolManager
