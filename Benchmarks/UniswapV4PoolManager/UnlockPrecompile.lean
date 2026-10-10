import Benchmarks.UniswapV4PoolManager.PrecompileReply
import Benchmarks.UniswapV4PoolManager.UnlockCallbackPrefix
import Benchmarks.UniswapV4PoolManager.CallGasEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem ZeroCallGasEvidence.unlock_precompile_size {evm evm' : State}
    {target : AccountAddress} {data out : ByteArray} {z : Bool}
    (w : ZeroCallGasEvidence evm target (unlockCallbackSelector++bytesReturnEncoding data) evm' z out)
    (hp : target ∈ π) (hb : BytesReturnBounds out) : out.size ≤ 64 := by
  have ht := w.theta.symm
  have he : toExecute evm.accountMap target = .Precompiled target := by
    unfold toExecute
    rw [if_pos hp]
  rw [he] at ht
  have hfirst : 2^132 ≤ nat_of_slice (unlockCallbackSelector++bytesReturnEncoding data) 0 32 := by
    rw [unlockCallbackRequest_firstWord]
    decide +kernel
  rcases thetaPrecompile_reply hfirst ht with hs | ho
  · exact hs
  · rw [ho] at hb
    exact (unlockCallbackRequest_not_return data hb).elim

end Benchmarks.UniswapV4PoolManager
