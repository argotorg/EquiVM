import Benchmarks.UniswapV4PoolManager.PoolSwapStepInitSource
import Benchmarks.UniswapV4PoolManager.PoolSwapMemory
import Benchmarks.UniswapV4PoolManager.PoolKeyMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapStepZeroMem (mem : ByteArray) (step : UInt256) : ByteArray :=
  wordSequenceMemory (writeWord mem 64 (step+UInt256.ofNat 256)) step.toNat
    [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]

def poolSwapStepInitMem (mem : ByteArray) (evm : State) (id step : UInt256) (zeroForOne : Bool) : ByteArray :=
  wordSequenceMemory (writeWord mem 64 (step+UInt256.ofNat 256)) step.toNat
    (poolSwapStepWordList (poolSwapInitialStep evm id zeroForOne))

theorem poolSwapStepInitMem_eq (mem : ByteArray) (evm : State) (id step : UInt256) (zeroForOne : Bool)
    (hf : step.toNat+256 < UInt256.size) :
    writeWord (poolSwapStepZeroMem mem step) (step+UInt256.ofNat 224).toNat
      (poolSwapInitialStep evm id zeroForOne).feeGrowthGlobal = poolSwapStepInitMem mem evm id step zeroForOne := by
  have hn := uadd_word_ofNat_toNat step 224 (by omega)
  simp only [poolSwapStepZeroMem, poolSwapStepInitMem, poolSwapInitialStep, poolSwapZeroStep,
    poolSwapStepWordList, wordSequenceMemory, hn, Nat.add_assoc]
  rfl

def poolSwapStepZeroAW (aw step : UInt256) : UInt256 :=
  M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) ⟨32⟩) step ⟨32⟩)
    (step+UInt256.ofNat 32) ⟨32⟩) (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 96) ⟨32⟩)
    (step+UInt256.ofNat 128) ⟨32⟩) (step+UInt256.ofNat 160) ⟨32⟩) (step+UInt256.ofNat 192) ⟨32⟩

def poolSwapStepFillAW (aw step : UInt256) : UInt256 := M (poolSwapStepZeroAW aw step) (step+UInt256.ofNat 224) ⟨32⟩

end Benchmarks.UniswapV4PoolManager
