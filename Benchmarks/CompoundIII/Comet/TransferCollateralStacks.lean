import Benchmarks.CompoundIII.Comet.TransferCollateralTrace
import Benchmarks.CompoundIII.Comet.CollateralMappingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def transferCollateralMemory (mem : ByteArray) (src dst asset : AccountAddress) : ByteArray :=
  userCollateralMemory (userCollateralMemory mem src asset) dst asset

theorem transferCollateralMemory_size {mem : ByteArray} (src dst asset : AccountAddress)
    (hm : 64 ≤ mem.size) : (transferCollateralMemory mem src dst asset).size = mem.size := by
  rw [transferCollateralMemory, userCollateralMemory_size _ _
    (by rw [userCollateralMemory_size _ _ hm]; exact hm), userCollateralMemory_size _ _ hm]

theorem transferCollateralMemory_free {mem : ByteArray} {free : UInt256}
    (src dst asset : AccountAddress) (hm : 96 ≤ mem.size) (hf : memLoad ⟨64⟩ mem = free) :
    memLoad ⟨64⟩ (transferCollateralMemory mem src dst asset) = free :=
  userCollateralMemory_free dst asset
    (by rw [userCollateralMemory_size _ _ (by omega)]; exact hm)
    (userCollateralMemory_free src asset hm hf)

def transferCollateralSubStack (src dst asset : AccountAddress)
    (amount srcBalance dstBalance ret : UInt256) (R : List UInt256) : List UInt256 :=
  [srcBalance, amount, ⟨15425⟩, dstBalance, srcBalance, EVM.word dst.val, EVM.word src.val,
    solcAddrMask, EVM.word asset.val, EVM.word src.val, EVM.word dst.val, amount, ret] ++ R

def transferCollateralWriteStack (src dst asset : AccountAddress)
    (amount srcBalance srcNext dstBalance dstNext ret : UInt256) (R : List UInt256) : List UInt256 :=
  [dstNext, srcNext, dstBalance, srcBalance, EVM.word dst.val, EVM.word src.val,
    solcAddrMask, EVM.word asset.val, EVM.word src.val, EVM.word dst.val, amount, ret] ++ R

def transferCollateralReadyStack (src dst asset : AccountAddress)
    (amount srcBalance srcNext dstBalance dstNext ret : UInt256) (R : List UInt256) : List UInt256 :=
  [srcBalance, srcNext, dstBalance, dstNext, EVM.word dst.val, EVM.word src.val,
    solcAddrMask, EVM.word asset.val, EVM.word src.val, EVM.word dst.val, amount, ret] ++ R

def transferCollateralDstStack (src dst asset : AccountAddress)
    (ptr amount dstBalance dstNext ret : UInt256) (R : List UInt256) : List UInt256 :=
  [ptr, dstBalance, dstNext, EVM.word dst.val, EVM.word src.val, solcAddrMask,
    EVM.word asset.val, EVM.word src.val, EVM.word dst.val, amount, ret] ++ R

def transferCollateralCheckStack (src dst asset : AccountAddress)
    (amount ret : UInt256) (R : List UInt256) : List UInt256 :=
  [EVM.word src.val, solcAddrMask, EVM.word asset.val, EVM.word src.val, EVM.word dst.val,
    amount, ret] ++ R

end Benchmarks.CompoundIII.Comet
