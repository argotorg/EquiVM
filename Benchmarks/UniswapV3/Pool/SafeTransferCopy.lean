import Benchmarks.UniswapV3.Pool.SafeTransferCopyMemory
import Benchmarks.UniswapV3.Pool.SafeTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem transferCopyWordsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15331⟩
      ((p + ⟨32⟩) :: (p + ⟨100⟩) :: ⟨68⟩ :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw (p + ⟨100⟩)) (hb : p.toNat + 196 ≤ 2 ^ 200)
    (hov : R.length + 5 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15362⟩
      ((p + ⟨96⟩) :: (p + ⟨164⟩) :: ⟨4⟩ :: R) (transferCopyMem2 mem p) aw' rdata σ k' C' ∧
      HeapMemory (transferCopyMem2 mem p) aw' (p + ⟨100⟩) := by
  have hoff (n : Nat) (hn : n ≤ 196) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 := hoff 32 (by decide)
  have h64 : (p + (⟨64⟩ : UInt256)).toNat = p.toNat + 64 := hoff 64 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have h132 : (p + (⟨132⟩ : UInt256)).toNat = p.toNat + 132 := hoff 132 (by decide)
  have hadd (n : UInt256) : UInt256.ofNat 32 + (p + n) = p + (UInt256.ofNat 32 + n) := by
    rw [← u256_add_assoc, u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
  have rdCopy1 := uniswapV3Pool_block_15331_fallthrough (immWords := wordsOf (immStore v))
    hov (by decide +kernel) rd
  have rdLoop := uniswapV3Pool_block_15340 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy1
  simp only [uniswapV3Pool_block_15340_stack, uniswapV3Pool_block_15340_memory, hadd,
    show UInt256.ofNat 32 + (⟨32⟩ : UInt256) = ⟨64⟩ from by decide +kernel,
    show UInt256.ofNat 32 + (⟨100⟩ : UInt256) = ⟨132⟩ from by decide +kernel,
    show (⟨68⟩ : UInt256) + UInt256.lnot (UInt256.ofNat 31) = ⟨36⟩ from by decide +kernel,
    h100] at rdLoop
  have hm1 := (hm.expand32 (p + ⟨32⟩) (by rw [h32]; omega)).cursor.writeAbove
    (p + ⟨100⟩) (memLoad (p + ⟨32⟩) mem) (le_refl _) (by rw [h100]; omega)
  rw [h100] at hm1
  change HeapMemory (transferCopyMem1 mem p) _ (p + ⟨100⟩) at hm1
  have rdCopy2 := uniswapV3Pool_block_15331_fallthrough (immWords := wordsOf (immStore v))
    hov (by decide +kernel) rdLoop
  have rdTail := uniswapV3Pool_block_15340 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdCopy2
  simp only [uniswapV3Pool_block_15340_stack, uniswapV3Pool_block_15340_memory, hadd,
    show UInt256.ofNat 32 + (⟨64⟩ : UInt256) = ⟨96⟩ from by decide +kernel,
    show UInt256.ofNat 32 + (⟨132⟩ : UInt256) = ⟨164⟩ from by decide +kernel,
    show (⟨36⟩ : UInt256) + UInt256.lnot (UInt256.ofNat 31) = ⟨4⟩ from by decide +kernel,
    h132] at rdTail
  have hm2 := (hm1.expand32 (p + ⟨64⟩) (by rw [h64]; omega)).cursor.writeAbove
    (p + ⟨132⟩) (memLoad (p + ⟨64⟩) (transferCopyMem1 mem p))
    (by rw [h100, h132]; omega) (by rw [h132]; omega)
  rw [h132] at hm2
  have rdDone := uniswapV3Pool_block_15331_taken (immWords := wordsOf (immStore v))
    hov (by decide +kernel) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdTail
  exact ⟨_, _, _, rdDone, hm2⟩

theorem transferCopyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p token : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15331⟩
      ((p + ⟨32⟩) :: (p + ⟨100⟩) :: ⟨68⟩ :: ⟨68⟩ :: (p + ⟨32⟩) ::
        (p + ⟨100⟩) :: (p + ⟨100⟩) :: p :: token :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw (p + ⟨100⟩)) (hb : p.toNat + 196 ≤ 2 ^ 200)
    (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15413⟩
      (gasArg :: token :: ⟨0⟩ :: (p + ⟨100⟩) :: ⟨68⟩ :: (p + ⟨100⟩) :: ⟨0⟩ ::
        (UInt256.ofNat 68 + (p + ⟨100⟩)) :: token :: R)
      (transferCopyMem3 mem p) aw' rdata σ k' C' ∧
      HeapMemory (transferCopyMem3 mem p) aw' (p + ⟨100⟩) := by
  obtain ⟨aw2, k2, C2, rdTail, hm2⟩ := transferCopyWordsX (v := v) rd hm hb (by evm_ov)
  have hoff (n : Nat) (hn : n ≤ 196) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h96 : (p + (⟨96⟩ : UInt256)).toNat = p.toNat + 96 := hoff 96 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have h164 : (p + (⟨164⟩ : UInt256)).toNat = p.toNat + 164 := hoff 164 (by decide)
  have hmask : UInt256.sub
      (UInt256.exp (UInt256.ofNat 256) (UInt256.sub (UInt256.ofNat 32) ⟨4⟩))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hmRead1 := hm2.expand32 (p + ⟨96⟩) (by rw [h96]; omega)
  have hmRead2 := hmRead1.expand32 (p + ⟨164⟩) (by rw [h164]; omega)
  have hmWrite := hmRead2.cursor.writeAbove (p + ⟨164⟩)
    (spliceWord4 (memLoad (p + ⟨96⟩) (transferCopyMem2 mem p))
      (memLoad (p + ⟨164⟩) (transferCopyMem2 mem p)))
    (by rw [h100, h164]; omega) (by rw [h164]; omega)
  rw [h164] at hmWrite
  change HeapMemory (transferCopyMem3 mem p) _ (p + ⟨100⟩) at hmWrite
  have hm3 := hmWrite.expand32 (UInt256.ofNat 64) (by decide)
  have hload : memLoad (UInt256.ofNat 64) (transferCopyMem3 mem p) = p + ⟨100⟩ := hm3.load64
  have hlen : UInt256.sub ((⟨68⟩ : UInt256) + (p + ⟨100⟩)) (p + ⟨100⟩) = ⟨68⟩ := by
    rw [u256_add_comm]
    exact word_add_sub_left _ _
  have rdCall := uniswapV3Pool_block_15362 (immWords := wordsOf (immStore v)) hov rdTail
  simp only [uniswapV3Pool_block_15362_stack, uniswapV3Pool_block_15362_memory, hmask, h164]
    at rdCall
  have hmemEq : (spliceWord4 (memLoad (p + ⟨96⟩) (transferCopyMem2 mem p))
      (memLoad (p + ⟨164⟩) (transferCopyMem2 mem p))).toByteArray.write 0
      (transferCopyMem2 mem p) (p.toNat + 164) 32 = transferCopyMem3 mem p := rfl
  rw [← spliceWord4, hmemEq, hload, hlen] at rdCall
  exact ⟨_, _, _, _, rdCall, hm3⟩

end Benchmarks.UniswapV3.Pool
