import Benchmarks.UniswapV4PoolManager.TickScanNextWords
import Benchmarks.UniswapV4PoolManager.TickScanMask
import Benchmarks.UniswapV4PoolManager.TickPositionWords
import Benchmarks.UniswapV4PoolManager.TickCompressWords
import Benchmarks.UniswapV4PoolManager.TickBitmapStorage
import Benchmarks.UniswapV4PoolManager.MostSignificantBit
import Benchmarks.UniswapV4PoolManager.LeastSignificantBit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickScanCompressed (tick spacing : UInt256) (lte : Bool) : UInt256 :=
  if lte then tickCompressRaw tick spacing else tickCompressRaw tick spacing + UInt256.ofNat 1

def tickScanMasked (evm : EVM.State) (id compressed : UInt256) (lte : Bool) : UInt256 :=
  UInt256.land (tickBitmapWord evm id (EVM.signed (tickPositionWord compressed)))
    (tickScanMask (tickPositionBit compressed) lte)

def tickScanIndex (masked : UInt256) (lte : Bool) : UInt256 :=
  if lte then mostSignificantBit masked else leastSignificantBit masked

def tickScanResultWord (compressed spacing masked : UInt256) (lte : Bool) : UInt256 :=
  tickScanNextWord compressed spacing
    (if masked = ⟨0⟩ then tickScanDefaultDistance (tickPositionBit compressed) lte
     else tickScanDistance (tickPositionBit compressed) (tickScanIndex masked lte) lte) lte

def tickScanResultValues (compressed spacing masked : UInt256) (lte : Bool) : List Value :=
  [.int (EVM.signed (tickScanResultWord compressed spacing masked lte)), .bool (decide (masked ≠ ⟨0⟩))]

def tickScanValues (evm : EVM.State) (id tick spacing : UInt256) (lte : Bool) : List Value :=
  tickScanResultValues (tickScanCompressed tick spacing lte) spacing
    (tickScanMasked evm id (tickScanCompressed tick spacing lte) lte) lte

theorem tickScanResultWord_canonical (compressed spacing masked : UInt256) (lte : Bool) :
    int24Canonical (tickScanResultWord compressed spacing masked lte) := tickScanNextWord_canonical _ _ _ _

end Benchmarks.UniswapV4PoolManager
