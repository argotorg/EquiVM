import Benchmarks.UniswapV3.Pool.ObserveEncodeMemory
import Benchmarks.UniswapV3.Pool.ObserveEncodeArithmetic
import Benchmarks.UniswapV3.Pool.ObserveCopyLoop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def observeEncodeFirstStack (i n : Nat) (s t p : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat (32 * i) :: (t + UInt256.ofNat 32) :: (p + UInt256.ofNat 96) ::
    UInt256.ofNat (32 * n) :: UInt256.ofNat (32 * n) :: (t + UInt256.ofNat 32) ::
    (p + UInt256.ofNat 96) :: (p + UInt256.ofNat 32) :: p :: p :: s :: t :: R

def observeEncodeSecondStack (i n m : Nat) (s t p : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat (32 * i) :: (s + UInt256.ofNat 32) :: (p + UInt256.ofNat (128 + 32 * n)) ::
    UInt256.ofNat (32 * m) :: UInt256.ofNat (32 * m) :: (s + UInt256.ofNat 32) ::
    (p + UInt256.ofNat (128 + 32 * n)) :: (p + UInt256.ofNat 32) :: p :: p :: s :: t :: R

theorem observeEncodeFirstHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw s t p : UInt256} {mem rdata : ByteArray}
    {xs : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1699⟩ (s :: t :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (ht : DynamicWordArrayMemory mem t xs)
    (htend : t.toNat + 32 * (xs.length + 1) ≤ p.toNat) (hb : p.toNat + 96 ≤ 2 ^ 200)
    (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', ActiveWords aw' ∧ RD (deployedRuntime v) ee g s0 ⟨1743⟩
      (observeEncodeFirstStack 0 xs.length s t p R) (observeEncodeFirstHead mem p xs.length)
      aw' rdata σ k' C' := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp64 := uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have h64 : UInt256.ofNat 32 + (UInt256.ofNat 32 + p) = p + UInt256.ofNat 64 :=
    wordAddNat_left_assoc p 32 32
  have h96 : UInt256.ofNat 32 + (p + UInt256.ofNat 64) = p + UInt256.ofNat 96 := by
    rw [u256_add_comm (UInt256.ofNat 32), wordAddNat_assoc]
  have ht1 := ht.write_disjoint p.toNat (UInt256.ofNat 64) (Or.inr (by
    simpa only [dynamicWordArrayWords, List.length_cons] using htend))
  have ht2 := ht1.write_disjoint (p.toNat + 64) (UInt256.ofNat xs.length) (Or.inr (by
    simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have hread1 := DynamicWordArrayMemory.header ht1 (by change _ < 2 ^ 256; omega)
  have hread2 := DynamicWordArrayMemory.header ht2 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_1699_memory (mem := mem) (x1 := t) =
      observeEncodeFirstHead mem p xs.length := by
    simp only [uniswapV3Pool_block_1699_memory, hload, h64, word_add_sub_left, hp64]
    change writeWord (writeWord mem p.toNat (UInt256.ofNat 64)) (p.toNat + 64)
      (memLoad t (writeWord mem p.toNat (UInt256.ofNat 64))) = _
    rw [hread1]
    rfl
  have hstack : uniswapV3Pool_block_1699_stack (mem := mem) (x0 := s) (x1 := t) (R := R) =
      observeEncodeFirstStack 0 xs.length s t p R := by
    simp only [uniswapV3Pool_block_1699_stack, hload, h64, h96, word_add_sub_left, hp64]
    change UInt256.ofNat 0 :: (UInt256.ofNat 32 + t) :: (p + UInt256.ofNat 96) ::
      UInt256.mul (UInt256.ofNat 32)
        (memLoad t (writeWord (writeWord mem p.toNat (UInt256.ofNat 64)) (p.toNat + 64)
          (memLoad t (writeWord mem p.toNat (UInt256.ofNat 64))))) ::
      UInt256.mul (UInt256.ofNat 32)
        (memLoad t (writeWord (writeWord mem p.toNat (UInt256.ofNat 64)) (p.toNat + 64)
          (memLoad t (writeWord mem p.toNat (UInt256.ofNat 64))))) ::
      (UInt256.ofNat 32 + t) :: (p + UInt256.ofNat 96) :: (UInt256.ofNat 32 + p) ::
      p :: p :: s :: t :: R = _
    simp only [hread1, hread2, wordNat_mul, u256_add_comm (UInt256.ofNat 32)]
    rfl
  have r1 := uniswapV3Pool_block_1699 (immWords := wordsOf (immStore v)) hov rd
  simp only [hstack, hmem, hload, h64] at r1
  refine ⟨_, _, _, ?_, r1⟩
  have ha1 := activeWords_expand32 hm.active (by decide : (UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200)
  have ha2 := activeWords_expand32 ha1 (show p.toNat + 32 ≤ 2 ^ 200 by omega)
  have ha3 := activeWords_expand32 ha2 (show t.toNat + 32 ≤ 2 ^ 200 by omega)
  have ha4 := activeWords_expand32 ha3 (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by
    rw [hp64]; omega)
  exact activeWords_expand32 ha4 (show t.toNat + 32 ≤ 2 ^ 200 by omega)

theorem observeEncodeSecondHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C n : Nat} {aw s t p : UInt256} {mem rdata : ByteArray}
    {ys : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1767⟩
      (observeEncodeFirstStack n n s t p R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (hs : DynamicWordArrayMemory mem s ys)
    (hsend : s.toNat + 32 * (ys.length + 1) ≤ p.toNat)
    (hb : p.toNat + 128 + 32 * n ≤ 2 ^ 200) (hov : R.length + 12 ≤ 1024) :
    ∃ aw' k' C', ActiveWords aw' ∧ RD (deployedRuntime v) ee g s0 ⟨1806⟩
      (observeEncodeSecondStack 0 n ys.length s t p R)
      (observeEncodeSecondHead mem p n ys.length) aw' rdata σ k' C' := by
  have hp32 := uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hpq : (p + UInt256.ofNat (96 + 32 * n)).toNat = p.toNat + 96 + 32 * n := by
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)]; omega
  have hq : UInt256.ofNat (32 * n) + (p + UInt256.ofNat 96) =
      p + UInt256.ofNat (96 + 32 * n) := by
    rw [u256_add_comm (UInt256.ofNat (32 * n)), wordAddNat_assoc]
  have h128 : UInt256.ofNat 32 + (p + UInt256.ofNat (96 + 32 * n)) =
      p + UInt256.ofNat (128 + 32 * n) := by
    rw [u256_add_comm (UInt256.ofNat 32), wordAddNat_assoc]
    congr 2
    omega
  have hs1 := hs.write_disjoint (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)) (Or.inr (by
    simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have hs2 := hs1.write_disjoint (p.toNat + 96 + 32 * n) (UInt256.ofNat ys.length) (Or.inr (by
    simp only [dynamicWordArrayWords, List.length_cons]; omega))
  have hread1 := DynamicWordArrayMemory.header hs1 (by change _ < 2 ^ 256; omega)
  have hread2 := DynamicWordArrayMemory.header hs2 (by change _ < 2 ^ 256; omega)
  have hmem : uniswapV3Pool_block_1767_memory (mem := mem)
      (x4 := UInt256.ofNat (32 * n)) (x6 := p + UInt256.ofNat 96)
      (x7 := p + UInt256.ofNat 32) (x9 := p) (x10 := s) =
      observeEncodeSecondHead mem p n ys.length := by
    simp only [uniswapV3Pool_block_1767_memory, hq, word_add_sub_left, hp32, hpq]
    change writeWord (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))
      (p.toNat + 96 + 32 * n)
      (memLoad s (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))) = _
    rw [hread1]
    rfl
  have hstack : uniswapV3Pool_block_1767_stack (mem := mem)
      (x4 := UInt256.ofNat (32 * n)) (x6 := p + UInt256.ofNat 96)
      (x7 := p + UInt256.ofNat 32) (x8 := p) (x9 := p) (x10 := s) (R := t :: R) =
      observeEncodeSecondStack 0 n ys.length s t p R := by
    simp only [uniswapV3Pool_block_1767_stack, hq, h128, word_add_sub_left, hp32, hpq]
    change UInt256.ofNat 0 :: (UInt256.ofNat 32 + s) :: (p + UInt256.ofNat (128 + 32 * n)) ::
      UInt256.mul (UInt256.ofNat 32)
        (memLoad s (writeWord (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))
          (p.toNat + 96 + 32 * n)
          (memLoad s (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))))) ::
      UInt256.mul (UInt256.ofNat 32)
        (memLoad s (writeWord (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))
          (p.toNat + 96 + 32 * n)
          (memLoad s (writeWord mem (p.toNat + 32) (UInt256.ofNat (96 + 32 * n)))))) ::
      (UInt256.ofNat 32 + s) :: (p + UInt256.ofNat (128 + 32 * n)) ::
      (p + UInt256.ofNat 32) :: p :: p :: s :: t :: R = _
    simp only [hread1, hread2, wordNat_mul, u256_add_comm (UInt256.ofNat 32)]
    rfl
  have r1 := uniswapV3Pool_block_1767 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega) rd
  simp only [hstack, hmem, hq] at r1
  refine ⟨_, _, _, ?_, r1⟩
  have ha1 := activeWords_expand32 hm.active (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by
    rw [hp32]; omega)
  have ha2 := activeWords_expand32 ha1 (show s.toNat + 32 ≤ 2 ^ 200 by omega)
  have ha3 := activeWords_expand32 ha2
    (show (p + UInt256.ofNat (96 + 32 * n)).toNat + 32 ≤ 2 ^ 200 by rw [hpq]; omega)
  exact activeWords_expand32 ha3 (show s.toNat + 32 ≤ 2 ^ 200 by omega)

end Benchmarks.UniswapV3.Pool
