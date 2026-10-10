import Benchmarks.UniswapV3.Pool.SwapCallbackEncoding
import Benchmarks.UniswapV3.Pool.SwapBalanceBefore
import Benchmarks.UniswapV3.Pool.CallbackBuildLayout
import Benchmarks.UniswapV3.Pool.CallbackMemory
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_018
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCallbackEntry (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4685⟩ else ⟨4987⟩

def swapCallbackSelector : UInt256 := UInt256.shiftLeft ⟨4198899251⟩ ⟨224⟩

def swapCallbackMem (mem : ByteArray) (p amount0 amount1 : UInt256) (cd : ByteArray)
    (start len : UInt256) : ByteArray :=
  callbackMem mem p.toNat swapCallbackSelector amount0 amount1 cd start.toNat len.toNat

theorem swapCallbackMem_read (mem : ByteArray) (p amount0 amount1 : UInt256) (cd : ByteArray)
    (start len : UInt256) (hc : start.toNat + len.toNat ≤ cd.size) (hl : len.toNat ≤ 2 ^ 32) :
    (swapCallbackMem mem p amount0 amount1 cd start len).readWithPadding p.toNat
      (132 + paddedSize len.toNat) =
      swapCallbackCalldata amount0 amount1 (cd.extract start.toNat (start.toNat + len.toNat)) := by
  rw [swapCallbackMem, callbackMem_read _ _ _ _ _ _ _ _ hc (by omega)]
  exact congrArg (fun x ↦ x ++ wordPairBytesPayload amount0 amount1
    (cd.extract start.toNat (start.toNat + len.toNat))) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem swapCallbackBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p bal amount0 amount1 junk0 junk1 junk2 junk3 junk4 len start :
      UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapBalanceBeforeReturn zeroForOne)
      (bal :: junk0 :: junk1 :: junk2 :: junk3 :: junk4 :: amount1 :: amount0 :: len :: start :: R)
        mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hc : start.toNat + len.toNat ≤ ee.calldata.size)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) (hov : R.length + 23 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (swapCallbackEntry zeroForOne)
      (len :: start :: (p + ⟨132⟩) :: (p + ⟨68⟩) :: (p + ⟨4⟩) ::
        len :: start :: amount1 :: amount0 :: ⟨4198899251⟩ :: EVM.word ee.source.val ::
        bal :: junk1 :: junk2 :: junk3 :: junk4 :: amount1 :: amount0 :: len :: start :: R)
      (swapCallbackMem mem p amount0 amount1 ee.calldata start len) aw' rdata σ k' C' ∧
      HeapMemory (swapCallbackMem mem p amount0 amount1 ee.calldata start len) aw' p := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  obtain ⟨hadd, h4, hoff, hend, h96⟩ := callbackWordOffsets p len hb
  have h4n : (p + (⟨4⟩ : UInt256)).toNat = p.toNat + 4 := hoff 4 (by decide)
  have h36 : (p + (⟨36⟩ : UInt256)).toNat = p.toNat + 36 := hoff 36 (by decide)
  have h68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 := hoff 68 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 := hoff 132 (by decide)
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  have hcaller : UInt256.land solcAddrMask (UInt256.ofNat ee.source.val) =
      EVM.word ee.source.val := by rw [u256_land_comm]; exact addressWord_val_clean _
  have hselector : UInt256.shiftLeft
      (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 4198899251)) (UInt256.ofNat 224) =
      swapCallbackSelector := by decide +kernel
  have hmem : (UInt256.ofNat 0).toByteArray.write 0
      (ee.calldata.write start.toNat (len.toByteArray.write 0
        ((⟨96⟩ : UInt256).toByteArray.write 0 (amount1.toByteArray.write 0
          (amount0.toByteArray.write 0 (swapCallbackSelector.toByteArray.write 0 mem p.toNat 32)
            (p.toNat + 4) 32) (p.toNat + 36) 32) (p.toNat + 68) 32)
          (p.toNat + 100) 32) (p.toNat + 132) len.toNat) (p.toNat + 132 + len.toNat) 32 =
      swapCallbackMem mem p amount0 amount1 ee.calldata start len := by
    simp only [swapCallbackMem, callbackMem, callbackCopyMem, callbackHeadMem, writeWordArray,
      Nat.add_assoc, u256_ofNat_toNat]
    rfl
  cases zeroForOne
  case' false =>
    have rdBuilt := uniswapV3Pool_block_4904 (immWords := wordsOf (immStore v)) hov rd
  case' true =>
    have rdBuilt := uniswapV3Pool_block_4602 (immWords := wordsOf (immStore v)) hov rd
  all_goals
    simp only [uniswapV3Pool_block_4602_stack, uniswapV3Pool_block_4602_memory,
      uniswapV3Pool_block_4904_stack, uniswapV3Pool_block_4904_memory, hload,
      h4, hadd, show UInt256.ofNat 32 + (⟨4⟩ : UInt256) = ⟨36⟩ from by decide +kernel,
      show UInt256.ofNat 32 + (⟨36⟩ : UInt256) = ⟨68⟩ from by decide +kernel,
      show UInt256.ofNat 32 + (⟨68⟩ : UInt256) = ⟨100⟩ from by decide +kernel,
      show UInt256.ofNat 32 + (⟨100⟩ : UInt256) = ⟨132⟩ from by decide +kernel,
      h96, hmask, hcaller, hselector, h4n, h36, h68, h100, h132, hend, hmem] at rdBuilt
    exact ⟨_, _, _, rdBuilt, callbackBuildHeap swapCallbackSelector amount0 amount1
      ee.calldata start len hm hc hb⟩

end Benchmarks.UniswapV3.Pool
