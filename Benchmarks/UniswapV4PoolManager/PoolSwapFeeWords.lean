import Benchmarks.UniswapV4PoolManager.PoolSwapStepWords
import Benchmarks.UniswapV4PoolManager.SimpleMulDivWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapProtocolShare (s : PoolSwapStepWords) (fee protocol : UInt256) : UInt256 :=
  if fee = protocol then s.feeAmount
  else UInt256.div (UInt256.mul (s.amountIn + s.feeAmount) protocol) (UInt256.ofNat 1000000)

def poolSwapProtocolStep (s : PoolSwapStepWords) (fee protocol : UInt256) : PoolSwapStepWords :=
  if protocol = ⟨0⟩ then s
  else {s with feeAmount := UInt256.sub s.feeAmount (poolSwapProtocolShare s fee protocol)}

def poolSwapProtocolAmount (s : PoolSwapStepWords) (fee protocol amount : UInt256) : UInt256 :=
  if protocol = ⟨0⟩ then amount else amount + poolSwapProtocolShare s fee protocol

def poolSwapGrowthStep (s : PoolSwapStepWords) (liquidity : UInt256) : PoolSwapStepWords :=
  if liquidity = ⟨0⟩ then s
  else {s with feeGrowthGlobal := s.feeGrowthGlobal + simpleMulDiv s.feeAmount (UInt256.ofNat (2^128)) liquidity}

end Benchmarks.UniswapV4PoolManager
