import Benchmarks.UniswapV3.Pool.ArrayReserve
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_054
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveAllocateArrayHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C n : Nat} {aw p dummy : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨17124⟩ else ⟨17055⟩)
      (dummy :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 32 * (n + 1) ≤ 2 ^ 200)
    (hov : R.length + 4 ≤ 1024) :
    RD (deployedRuntime v) ee g s0
      (if n = 0 then (if second then ⟨17166⟩ else ⟨17097⟩)
        else (if second then ⟨17151⟩ else ⟨17082⟩))
      (UInt256.ofNat n :: p :: R) (arrayReserveHead mem p n) (M aw p ⟨32⟩) rdata σ
      (k + 21) (C + (69 + memExpansionCost aw p ⟨32⟩)) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have ha1 := activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega)
  have h64' : M (M aw p ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩ = M aw p ⟨32⟩ := expandedWords64_eq ha1
  have hnext : p + (UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat n)) =
      wordArrayElement p n := (u256_add_comm p _).trans
        (wordArrayElement_raw p n (by change _ < 2 ^ 256; omega))
  have hsz : n < UInt256.size := by change _ < 2 ^ 256; omega
  by_cases hn : n = 0
  · subst n
    cases second with
    | false =>
      have r := uniswapV3Pool_block_17055_taken (immWords := wordsOf (immStore v)) hov (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [↓reduceIte, uniswapV3Pool_block_17055_taken_stack,
        uniswapV3Pool_block_17055_taken_memory, hload, hnext, h64, h64', memExpansionCost,
        Nat.sub_self, Nat.add_zero, arrayReserveHead, Reasoning.Theory.writeWord] using r
    | true =>
      have r := uniswapV3Pool_block_17124_taken (immWords := wordsOf (immStore v)) hov (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [↓reduceIte, uniswapV3Pool_block_17124_taken_stack,
        uniswapV3Pool_block_17124_taken_memory, hload, hnext, h64, h64', memExpansionCost,
        Nat.sub_self, Nat.add_zero, arrayReserveHead, Reasoning.Theory.writeWord] using r
  · have hw : UInt256.ofNat n ≠ (⟨0⟩ : UInt256) := by
      intro h
      have h' := congrArg UInt256.toNat h
      rw [ulit_toNat' n hsz] at h'
      exact hn h'
    cases second with
    | false =>
      have r := uniswapV3Pool_block_17055_fallthrough (immWords := wordsOf (immStore v)) hov
        (isZero_eq_zero_of_ne hw) rd
      simpa only [if_neg hn, ↓reduceIte, uniswapV3Pool_block_17055_fallthrough_stack,
        uniswapV3Pool_block_17055_fallthrough_memory, hload, hnext, h64, h64', memExpansionCost,
        Nat.sub_self, Nat.add_zero, arrayReserveHead, Reasoning.Theory.writeWord] using r
    | true =>
      have r := uniswapV3Pool_block_17124_fallthrough (immWords := wordsOf (immStore v)) hov
        (isZero_eq_zero_of_ne hw) rd
      simpa only [if_neg hn, ↓reduceIte, uniswapV3Pool_block_17124_fallthrough_stack,
        uniswapV3Pool_block_17124_fallthrough_memory, hload, hnext, h64, h64', memExpansionCost,
        Nat.sub_self, Nat.add_zero, arrayReserveHead, Reasoning.Theory.writeWord] using r

theorem oracleObserveAllocateArrayX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C n : Nat} {aw p dummy : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨17124⟩ else ⟨17055⟩)
      (dummy :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hb : p.toNat + 32 * (n + 1) ≤ 2 ^ 200)
    (hdata : ee.calldata.size < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ dummy' k' C', C + (Cₘ (arrayReserveAw aw p n) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨17166⟩ else ⟨17097⟩)
        (dummy' :: p :: R) (arrayReserveMem ee.calldata mem p n) (arrayReserveAw aw p n) rdata σ k' C' := by
  have r1 := oracleObserveAllocateArrayHeadX (v := v) second rd hm hb (by omega)
  by_cases hn : n = 0
  · subst n
    simp only [↓reduceIte] at r1
    have hmem : arrayReserveMem ee.calldata mem p 0 = arrayReserveHead mem p 0 :=
      byteArray_write_len_zero _ _ _ _
    have haw : arrayReserveAw aw p 0 = M aw p ⟨32⟩ := u256_ofNat_toNat _
    refine ⟨UInt256.ofNat 0, k + 21, C + (69 + memExpansionCost aw p ⟨32⟩), ?_, ?_⟩
    · rw [haw]; dsimp only [memExpansionCost]; omega
    · simpa only [hmem, haw] using r1
  · simp only [if_neg hn] at r1
    have hmul : UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32) = UInt256.ofNat (32 * n) := by
      apply u256_inj
      rw [u256_mul_toNat, ulit_toNat' n (by change _ < 2 ^ 256; omega),
        ulit_toNat' (32 * n) (by change _ < 2 ^ 256; omega)]
      change (n * 32) % UInt256.size = 32 * n
      rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
      omega
    have hp32' : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
      uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
    have hl : (UInt256.ofNat (32 * n)).toNat = 32 * n := ulit_toNat' _ (by change _ < 2 ^ 256; omega)
    have r2 : RD (deployedRuntime v) ee g s0 (if second then ⟨17166⟩ else ⟨17097⟩)
        ((UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32) + (UInt256.ofNat 32 + p)) :: p :: R)
        (ee.calldata.write (UInt256.ofNat ee.calldata.size).toNat (arrayReserveHead mem p n)
          (UInt256.ofNat 32 + p).toNat (UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32)).toNat)
        (M (M aw p ⟨32⟩) (UInt256.ofNat 32 + p) (UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32)))
        rdata σ (k + 21 + 13)
        (C + (69 + memExpansionCost aw p ⟨32⟩) +
          (36 + memExpansionCost (M aw p ⟨32⟩) (UInt256.ofNat 32 + p)
            (UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32)) +
              (3 + 3 * (((UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 32)).toNat + 31) / 32)))) := by
      cases second
      · exact uniswapV3Pool_block_17082 (immWords := wordsOf (immStore v)) hov r1
      · exact uniswapV3Pool_block_17151 (immWords := wordsOf (immStore v)) hov r1
    simp only [hmul, ulit_toNat' ee.calldata.size hdata, hp32', hl,
      u256_add_comm (UInt256.ofNat 32) p] at r2
    refine ⟨_, _, _, ?_, r2⟩
    dsimp only [arrayReserveAw, memExpansionCost]
    simp only [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from rfl]
    omega

end Benchmarks.UniswapV3.Pool
