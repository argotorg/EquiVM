import Benchmarks.UniswapV3.Pool.CallbackMemory
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashCallbackSelector : UInt256 := UInt256.shiftLeft ⟨3922440112⟩ ⟨224⟩

def flashCallbackMem (mem : ByteArray) (p fee0 fee1 : UInt256) (cd : ByteArray)
    (start len : UInt256) : ByteArray :=
  callbackMem mem p.toNat flashCallbackSelector fee0 fee1 cd start.toNat len.toNat

theorem flashCallbackMem_read (mem : ByteArray) (p fee0 fee1 : UInt256) (cd : ByteArray)
    (start len : UInt256) (hc : start.toNat + len.toNat ≤ cd.size) (hl : len.toNat ≤ 2 ^ 32) :
    (flashCallbackMem mem p fee0 fee1 cd start len).readWithPadding p.toNat
      (132 + paddedSize len.toNat) =
      flashCallbackCalldata fee0 fee1 (cd.extract start.toNat (start.toNat + len.toNat)) := by
  rw [flashCallbackMem, callbackMem_read _ _ _ _ _ _ _ _ hc (by omega)]
  exact congrArg (fun x ↦ x ++ wordPairBytesPayload fee0 fee1
    (cd.extract start.toNat (start.toNat + len.toNat))) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem flashCallbackBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p bal0 bal1 fee0 fee1 liquidity len start : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6827⟩
      (bal1 :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hc : start.toNat + len.toNat ≤ ee.calldata.size)
    (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200) (hov : R.length + 21 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨6911⟩
      (UInt256.lnot ⟨31⟩ :: len :: start :: (p + ⟨132⟩) :: (p + ⟨68⟩) :: (p + ⟨4⟩) ::
        len :: start :: fee1 :: fee0 :: ⟨3922440112⟩ :: EVM.word ee.source.val ::
        bal1 :: bal0 :: fee1 :: fee0 :: liquidity :: len :: start :: R)
      (flashCallbackMem mem p fee0 fee1 ee.calldata start len) aw' rdata σ k' C' ∧
      HeapMemory (flashCallbackMem mem p fee0 fee1 ee.calldata start len) aw' p := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hadd (n : UInt256) : UInt256.ofNat 32 + (p + n) = p + (UInt256.ofNat 32 + n) := by
    rw [← u256_add_assoc, u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
  have h4 : UInt256.ofNat 4 + p = p + ⟨4⟩ := u256_add_comm _ _
  have hoff (n : Nat) (hn : n ≤ 132) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h4n : (p + (⟨4⟩ : UInt256)).toNat = p.toNat + 4 := hoff 4 (by decide)
  have h36 : (p + (⟨36⟩ : UInt256)).toNat = p.toNat + 36 := hoff 36 (by decide)
  have h68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 := hoff 68 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 := hoff 132 (by decide)
  have hend : (p + (⟨132⟩ : UInt256) + len).toNat = p.toNat + 132 + len.toNat := by
    change (UInt256.add (p + ⟨132⟩) len).toNat = _
    rw [addWord_toNat _ _ (by rw [h132]; change _ < 2 ^ 256; omega), h132]
  have h96 : UInt256.sub (p + ⟨100⟩) (p + ⟨4⟩) = ⟨96⟩ := by
    have he : p + (⟨100⟩ : UInt256) = (p + ⟨4⟩) + ⟨96⟩ := by
      rw [u256_add_assoc]
      rfl
    rw [he, word_add_sub_left]
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide +kernel
  have hcaller : UInt256.land solcAddrMask (UInt256.ofNat ee.source.val) =
      EVM.word ee.source.val := by rw [u256_land_comm]; exact addressWord_val_clean _
  have hselector : UInt256.shiftLeft
      (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 3922440112)) (UInt256.ofNat 224) =
      flashCallbackSelector := by decide +kernel
  have rdBuilt := uniswapV3Pool_block_6827 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_6827_stack, uniswapV3Pool_block_6827_memory, hload,
    h4, hadd, show UInt256.ofNat 32 + (⟨4⟩ : UInt256) = ⟨36⟩ from by decide +kernel,
    show UInt256.ofNat 32 + (⟨36⟩ : UInt256) = ⟨68⟩ from by decide +kernel,
    show UInt256.ofNat 32 + (⟨68⟩ : UInt256) = ⟨100⟩ from by decide +kernel,
    show UInt256.ofNat 32 + (⟨100⟩ : UInt256) = ⟨132⟩ from by decide +kernel,
    h96, hmask, hcaller, hselector] at rdBuilt
  simp only [h4n, h36, h68, h100, h132, hend] at rdBuilt
  have hmem : (UInt256.ofNat 0).toByteArray.write 0
      (ee.calldata.write start.toNat (len.toByteArray.write 0
        ((⟨96⟩ : UInt256).toByteArray.write 0 (fee1.toByteArray.write 0
          (fee0.toByteArray.write 0 (flashCallbackSelector.toByteArray.write 0 mem p.toNat 32)
            (p.toNat + 4) 32) (p.toNat + 36) 32) (p.toNat + 68) 32)
          (p.toNat + 100) 32) (p.toNat + 132) len.toNat) (p.toNat + 132 + len.toNat) 32 =
      flashCallbackMem mem p fee0 fee1 ee.calldata start len := by
    simp only [flashCallbackMem, callbackMem, callbackCopyMem, callbackHeadMem, writeWordArray,
      Nat.add_assoc, u256_ofNat_toNat]
    rfl
  rw [hmem] at rdBuilt
  refine ⟨_, _, _, rdBuilt, ?_⟩
  refine ⟨?_, ?_, hm.lower, ?_, ?_⟩
  · rw [flashCallbackMem, callbackMem_size _ _ _ _ _ _ _ _ hc]; have hp := hm.lower; omega
  · exact (callbackMem_read64 _ _ _ _ _ _ _ _ hc (by have hp := hm.lower; omega) hm.size).trans hm.free
  · rw [flashCallbackMem, callbackMem_size _ _ _ _ _ _ _ _ hc]; omega
  · apply activeWords_expand32
    · apply activeWords_expand
      · repeat' apply activeWords_expand32
        all_goals first | exact hm.active | (change 64 + 32 ≤ _; omega) |
          (change (p + UInt256.ofNat _).toNat + 32 ≤ _; rw [hoff _ (by omega)]; omega) | omega
      · rw [h132]; omega
    · rw [hend]; omega

end Benchmarks.UniswapV3.Pool
