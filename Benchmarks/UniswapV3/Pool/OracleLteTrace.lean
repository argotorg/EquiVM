import Benchmarks.UniswapV3.Pool.OracleLteWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_068
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_069
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044
import Benchmarks.UniswapV3.Pool.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleLteAdjustedMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret timeRaw aRaw bRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (time a b : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20254⟩
      (⟨0⟩ :: bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ k C)
    (ht : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (ha : UInt256.land (UInt256.ofNat 4294967295) aRaw = a)
    (hb : UInt256.land (UInt256.ofNat 4294967295) bRaw = b)
    (hab : a.toNat < 2 ^ 32) (hbb : b.toNat < 2 ^ 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      ((if oracleAdjusted time a ≤ oracleAdjusted time b then ⟨1⟩ else ⟨0⟩) :: R)
      mem aw rdata σ k' C' := by
  have hA : ∃ kA CA, C ≤ CA ∧ RD (deployedRuntime v) ee g s0 ⟨20302⟩
      (UInt256.ofNat (oracleAdjusted time a) :: ⟨0⟩ :: ⟨0⟩ ::
        bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ kA CA := by
    by_cases h : time.toNat < a.toNat
    · have r1 := uniswapV3Pool_block_20254_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ha, ht, ugt_one h]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have r2 := uniswapV3Pool_block_20294 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      refine ⟨k + 11 + 4, C + 38 + 10, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20294_stack, uniswapV3Pool_block_20254_taken_stack,
        ha, oracleAdjustedWord_eq time a hab, if_pos h] using r2
    · have r1 := uniswapV3Pool_block_20254_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ha, ht, ugt_zero (by omega)]; rfl) rd
      have r2 := uniswapV3Pool_block_20276 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨k + 11 + 7, C + 38 + 26, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20276_stack, uniswapV3Pool_block_20254_fallthrough_stack,
        ha, oracleAdjustedWord_eq time a hab, if_neg h] using r2
  obtain ⟨kA, CA, hCA, rdA⟩ := hA
  have hB : ∃ kB CB, CA ≤ CB ∧ RD (deployedRuntime v) ee g s0 ⟨20359⟩
      (UInt256.ofNat (oracleAdjusted time b) :: ⟨0⟩ ::
        UInt256.ofNat (oracleAdjusted time a) :: ⟨0⟩ :: bRaw :: aRaw :: timeRaw :: ret :: R)
      mem aw rdata σ kB CB := by
    by_cases h : time.toNat < b.toNat
    · have r1 := uniswapV3Pool_block_20302_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hb, ht, ugt_one h]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdA
      have r2 := uniswapV3Pool_block_20351 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      refine ⟨kA + 15 + 4, CA + 49 + 10, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20351_stack, uniswapV3Pool_block_20302_taken_stack,
        hb, oracleAdjustedWord_clean time a hab, oracleAdjustedWord_eq time b hbb, if_pos h] using r2
    · have r1 := uniswapV3Pool_block_20302_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hb, ht, ugt_zero (by omega)]; rfl) rdA
      have r2 := uniswapV3Pool_block_20333 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨kA + 15 + 7, CA + 49 + 26, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20333_stack, uniswapV3Pool_block_20302_fallthrough_stack,
        hb, oracleAdjustedWord_clean time a hab, oracleAdjustedWord_eq time b hbb, if_neg h] using r2
  obtain ⟨kB, CB, hCB, rdB⟩ := hB
  have r := uniswapV3Pool_block_20359 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdB
  refine ⟨kB + 15, CB + 43, by omega, ?_⟩
  simpa only [uniswapV3Pool_block_20359_stack, oracleAdjustedWord_clean time b hbb,
    isZero_gt_le_word, oracleAdjustedWord_toNat time a hab,
    oracleAdjustedWord_toNat time b hbb] using r

theorem oracleLteMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret timeRaw aRaw bRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (time a b : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20184⟩
      (bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ k C)
    (ht : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (ha : UInt256.land (UInt256.ofNat 4294967295) aRaw = a)
    (hb : UInt256.land (UInt256.ofNat 4294967295) bRaw = b)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      ((if oracleLte time a b then ⟨1⟩ else ⟨0⟩) :: R) mem aw rdata σ k' C' := by
  have hcond : ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨20226⟩
      ((if a.toNat ≤ time.toNat ∧ b.toNat ≤ time.toNat then ⟨1⟩ else ⟨0⟩) ::
        ⟨0⟩ :: bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ k' C' := by
    by_cases h : a.toNat ≤ time.toNat
    · have r1 := uniswapV3Pool_block_20184_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ha, ht, ugt_zero h]; rfl) rd
      have r2 := uniswapV3Pool_block_20209 (immWords := wordsOf (immStore v)) (by evm_ov) r1
      refine ⟨k + 14 + 9, C + 47 + 26, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20209_stack, uniswapV3Pool_block_20184_fallthrough_stack,
        hb, ht, isZero_gt_le_word, h, true_and] using r2
    · have r1 := uniswapV3Pool_block_20184_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ha, ht, ugt_one (by omega)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      refine ⟨k + 14, C + 47, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20184_taken_stack, ha, ht, isZero_gt_le_word,
        if_neg h, h, false_and, ↓reduceIte] using r1
  obtain ⟨k1, C1, hC1, r1⟩ := hcond
  by_cases h : a.toNat ≤ time.toNat ∧ b.toNat ≤ time.toNat
  · rw [if_pos h] at r1
    have r2 := uniswapV3Pool_block_20226_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) r1
    have r3 := uniswapV3Pool_block_20232 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    have r4 := uniswapV3Pool_block_13186 (immWords := wordsOf (immStore v))
      (by evm_ov) hret r3
    refine ⟨k1 + 4 + 12 + 7, C1 + 17 + 40 + 21, by omega, ?_⟩
    simpa only [uniswapV3Pool_block_13186_stack, uniswapV3Pool_block_20232_stack,
      uniswapV3Pool_block_20226_fallthrough_stack, ha, hb, isZero_gt_le_word,
      oracleLte, if_pos h, Bool.decide_iff] using r4
  · rw [if_neg h] at r1
    have r2 := uniswapV3Pool_block_20226_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have hab : a.toNat < 2 ^ 32 := by
      rw [← ha, u256_land_comm]
      exact u256LandMaskToNatLtOfToNat _ _ (by decide)
    have hbb : b.toNat < 2 ^ 32 := by
      rw [← hb, u256_land_comm]
      exact u256LandMaskToNatLtOfToNat _ _ (by decide)
    obtain ⟨k2, C2, hC2, r3⟩ :=
      oracleLteAdjustedMonoX (v := v) time a b r2 ht ha hb hab hbb hret hov
    refine ⟨k2, C2, by omega, ?_⟩
    simpa only [oracleLte, if_neg h, Bool.decide_iff] using r3

theorem oracleLteAdjustedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret timeRaw aRaw bRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (time a b : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20254⟩
      (⟨0⟩ :: bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ k C)
    (ht : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (ha : UInt256.land (UInt256.ofNat 4294967295) aRaw = a)
    (hb : UInt256.land (UInt256.ofNat 4294967295) bRaw = b)
    (hab : a.toNat < 2 ^ 32) (hbb : b.toNat < 2 ^ 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      ((if oracleAdjusted time a ≤ oracleAdjusted time b then ⟨1⟩ else ⟨0⟩) :: R)
      mem aw rdata σ k' C'  := by
  obtain ⟨k, C, _, hout⟩ := oracleLteAdjustedMonoX (v := v) time a b rd ht ha hb hab hbb hret hov
  exact ⟨k, C, hout⟩

theorem oracleLteX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret timeRaw aRaw bRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (time a b : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20184⟩
      (bRaw :: aRaw :: timeRaw :: ret :: R) mem aw rdata σ k C)
    (ht : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (ha : UInt256.land (UInt256.ofNat 4294967295) aRaw = a)
    (hb : UInt256.land (UInt256.ofNat 4294967295) bRaw = b)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      ((if oracleLte time a b then ⟨1⟩ else ⟨0⟩) :: R) mem aw rdata σ k' C'  := by
  obtain ⟨k, C, _, hout⟩ := oracleLteMonoX (v := v) time a b rd ht ha hb hret hov
  exact ⟨k, C, hout⟩

end Benchmarks.UniswapV3.Pool
