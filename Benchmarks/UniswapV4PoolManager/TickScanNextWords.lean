import Benchmarks.UniswapV4PoolManager.WordNarrowCast

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickScanNextWord (compressed spacing distance : UInt256) (lte : Bool) : UInt256 :=
  UInt256.signextend (UInt256.ofNat 2) (UInt256.mul
    (UInt256.signextend (UInt256.ofNat 2)
      (if lte then UInt256.sub compressed (UInt256.signextend (UInt256.ofNat 2) distance)
       else UInt256.signextend (UInt256.ofNat 2) compressed + UInt256.signextend (UInt256.ofNat 2) distance))
    spacing)

def tickScanDefaultDistance (bit : UInt256) (lte : Bool) : UInt256 :=
  if lte then bit else UInt256.land (UInt256.sub (UInt256.ofNat 255) bit) (UInt256.ofNat 255)

def tickScanDistance (bit index : UInt256) (lte : Bool) : UInt256 :=
  UInt256.land (if lte then UInt256.sub bit index else UInt256.sub index bit) (UInt256.ofNat 255)

theorem tickScanNextWord_canonical (compressed spacing distance : UInt256) (lte : Bool) :
    int24Canonical (tickScanNextWord compressed spacing distance lte) := signextend24_canonical _

theorem tickScanDefaultDistance_fits {bit : UInt256} (hb : bit.toNat < 256) (lte : Bool) :
    (tickScanDefaultDistance bit lte).toNat < 256 := by
  cases lte with
  | true => exact hb
  | false => exact u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 255) (bits := 8) rfl

theorem tickScanDistance_fits (bit index : UInt256) (lte : Bool) :
    (tickScanDistance bit index lte).toNat < 256 :=
  u256LandMaskToNatLtOfToNat _ (UInt256.ofNat 255) (bits := 8) rfl

end Benchmarks.UniswapV4PoolManager
