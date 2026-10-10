import Benchmarks.UniswapV3.Pool.BalanceCopyMemory
import Benchmarks.UniswapV3.Pool.BalanceBuild
import Benchmarks.UniswapV3.Pool.SafeTransferCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem balanceCopyWordsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceBuildExit second)
      (⟨36⟩ :: (p + ⟨68⟩) :: p :: (p + ⟨32⟩) :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw (p + ⟨68⟩)) (hb : p.toNat + 132 ≤ 2 ^ 200)
    (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15725⟩
      ((p + ⟨64⟩) :: (p + ⟨100⟩) :: ⟨4⟩ :: ⟨36⟩ :: (p + ⟨32⟩) ::
        (p + ⟨68⟩) :: (p + ⟨68⟩) :: p :: R) (balanceCopyMem1 mem p) aw' rdata σ k' C' ∧
      HeapMemory (balanceCopyMem1 mem p) aw' (p + ⟨68⟩) := by
  have hoff (n : Nat) (hn : n ≤ 132) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h32 : (p + (⟨32⟩ : UInt256)).toNat = p.toNat + 32 := hoff 32 (by decide)
  have h68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 := hoff 68 (by decide)
  have hadd (n : UInt256) : UInt256.ofNat 32 + (p + n) = p + (UInt256.ofNat 32 + n) := by
    rw [← u256_add_assoc, u256_add_comm (UInt256.ofNat 32), u256_add_assoc]
  cases second
  all_goals first
    | have rdCheck := uniswapV3Pool_block_15684 (immWords := wordsOf (immStore v)) (by evm_ov) rd
      simp only [uniswapV3Pool_block_15684_stack] at rdCheck
      have rdBody := uniswapV3Pool_block_15694_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel) rdCheck
    | have rdBody := uniswapV3Pool_block_16013_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel) rd
      simp only [uniswapV3Pool_block_16013_fallthrough_stack] at rdBody
  all_goals first
    | have rdLoop := uniswapV3Pool_block_15703 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdBody
    | have rdLoop := uniswapV3Pool_block_16031 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdBody
  all_goals
    simp only [uniswapV3Pool_block_15703_stack, uniswapV3Pool_block_15703_memory,
      uniswapV3Pool_block_16031_stack, uniswapV3Pool_block_16031_memory, hadd,
      show UInt256.ofNat 32 + (⟨32⟩ : UInt256) = ⟨64⟩ from by decide +kernel,
      show UInt256.ofNat 32 + (⟨68⟩ : UInt256) = ⟨100⟩ from by decide +kernel,
      show (⟨36⟩ : UInt256) + UInt256.lnot (UInt256.ofNat 31) = ⟨4⟩ from by decide +kernel,
      h68] at rdLoop
    have hm1 := (hm.expand32 (p + ⟨32⟩) (by rw [h32]; omega)).cursor.writeAbove
      (p + ⟨68⟩) (memLoad (p + ⟨32⟩) mem) (le_refl _) (by rw [h68]; omega)
    rw [h68] at hm1
    have rdDone := uniswapV3Pool_block_15694_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLoop
    exact ⟨_, _, _, rdDone, hm1⟩

theorem balanceCopyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p token : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (balanceBuildExit second)
      (⟨36⟩ :: (p + ⟨68⟩) :: p :: (p + ⟨32⟩) :: token :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw (p + ⟨68⟩)) (hb : p.toNat + 132 ≤ 2 ^ 200)
    (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15774⟩
      (gasArg :: token :: (p + ⟨68⟩) :: ⟨36⟩ :: (p + ⟨68⟩) :: ⟨0⟩ ::
        (UInt256.ofNat 36 + (p + ⟨68⟩)) :: token :: R)
      (balanceCopyMem2 mem p) aw' rdata σ k' C' ∧
      HeapMemory (balanceCopyMem2 mem p) aw' (p + ⟨68⟩) := by
  obtain ⟨aw1, k1, C1, rdTail, hm1⟩ := balanceCopyWordsX (v := v) second rd hm hb (by evm_ov)
  have hoff (n : Nat) (hn : n ≤ 132) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have h64 : (p + (⟨64⟩ : UInt256)).toNat = p.toNat + 64 := hoff 64 (by decide)
  have h68 : (p + (⟨68⟩ : UInt256)).toNat = p.toNat + 68 := hoff 68 (by decide)
  have h100 : (p + (⟨100⟩ : UInt256)).toNat = p.toNat + 100 := hoff 100 (by decide)
  have hmask : UInt256.sub
      (UInt256.exp (UInt256.ofNat 256) (UInt256.sub (UInt256.ofNat 32) ⟨4⟩))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 224 - 1) := by decide +kernel
  have hmRead1 := hm1.expand32 (p + ⟨64⟩) (by rw [h64]; omega)
  have hmRead2 := hmRead1.expand32 (p + ⟨100⟩) (by rw [h100]; omega)
  have hmWrite := hmRead2.cursor.writeAbove (p + ⟨100⟩)
    (spliceWord4 (memLoad (p + ⟨64⟩) (balanceCopyMem1 mem p))
      (memLoad (p + ⟨100⟩) (balanceCopyMem1 mem p)))
    (by rw [h68, h100]; omega) (by rw [h100]; omega)
  rw [h100] at hmWrite
  change HeapMemory (balanceCopyMem2 mem p) _ (p + ⟨68⟩) at hmWrite
  have hm2 := hmWrite.expand32 (UInt256.ofNat 64) (by decide)
  have hload : memLoad (UInt256.ofNat 64) (balanceCopyMem2 mem p) = p + ⟨68⟩ := hm2.load64
  have hlen : UInt256.sub ((⟨36⟩ : UInt256) + (p + ⟨68⟩)) (p + ⟨68⟩) = ⟨36⟩ := by
    rw [u256_add_comm]
    exact word_add_sub_left _ _
  have rdCall := uniswapV3Pool_block_15725 (immWords := wordsOf (immStore v)) hov rdTail
  simp only [uniswapV3Pool_block_15725_stack, uniswapV3Pool_block_15725_memory, hmask, h100] at rdCall
  have hmemEq : (spliceWord4 (memLoad (p + ⟨64⟩) (balanceCopyMem1 mem p))
      (memLoad (p + ⟨100⟩) (balanceCopyMem1 mem p))).toByteArray.write 0
      (balanceCopyMem1 mem p) (p.toNat + 100) 32 = balanceCopyMem2 mem p := rfl
  rw [← spliceWord4, hmemEq, hload, hlen] at rdCall
  exact ⟨_, _, _, _, rdCall, hm2⟩

end Benchmarks.UniswapV3.Pool
