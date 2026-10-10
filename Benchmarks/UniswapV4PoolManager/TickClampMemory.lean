import Benchmarks.UniswapV4PoolManager.TickClampWords
import Benchmarks.UniswapV4PoolManager.SparseBytesMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickScanStoreMemory (mem : ByteArray) (step tick : UInt256) (initialized : Bool) : ByteArray :=
  writeWord (writeWord mem (step+UInt256.ofNat 64).toNat initialized.toUInt256)
    (step+UInt256.ofNat 32).toNat (UInt256.signextend (UInt256.ofNat 2) tick)

def tickClampLowerMemory (mem : ByteArray) (step tick : UInt256) (initialized : Bool) : ByteArray :=
  let m := tickScanStoreMemory mem step tick initialized
  if EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick) ≤ -887272 then
    writeWord m (step+UInt256.ofNat 32).toNat tickMinWord else m

def tickClampMemory (mem : ByteArray) (step tick : UInt256) (initialized : Bool) : ByteArray :=
  let m := tickClampLowerMemory mem step tick initialized
  if EVM.signed (tickClampLowerWord tick) ≥ 887272 then
    writeWord m (step+UInt256.ofNat 32).toNat tickMaxWord else m

theorem tickScanStoreMemory_tick (mem : ByteArray) (step tick : UInt256) (initialized : Bool) :
    memLoad (step+UInt256.ofNat 32) (tickScanStoreMemory mem step tick initialized) =
      UInt256.signextend (UInt256.ofNat 2) tick := writeWord_sparse_load_back ..

theorem tickClampLowerMemory_tick (mem : ByteArray) (step tick : UInt256) (initialized : Bool) :
    memLoad (step+UInt256.ofNat 32) (tickClampLowerMemory mem step tick initialized) =
      tickClampLowerWord tick := by
  unfold tickClampLowerMemory tickClampLowerWord
  dsimp only
  split
  · exact writeWord_sparse_load_back ..
  · exact tickScanStoreMemory_tick ..

theorem tickClampMemory_tick (mem : ByteArray) (step tick : UInt256) (initialized : Bool) :
    memLoad (step+UInt256.ofNat 32) (tickClampMemory mem step tick initialized) = tickClampWord tick := by
  unfold tickClampMemory tickClampWord
  dsimp only
  split
  · exact writeWord_sparse_load_back ..
  · exact tickClampLowerMemory_tick ..

end Benchmarks.UniswapV4PoolManager
