import Benchmarks.UniswapV3.Pool.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def poolLiquidityWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWordAt ⟨4⟩ σ I) (UInt256.ofNat (2 ^ 128 - 1))

theorem poolLiquidityWord_lt (σ : AccountMap) (I : ExecutionEnv) :
    (poolLiquidityWord σ I).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

end Benchmarks.UniswapV3.Pool
