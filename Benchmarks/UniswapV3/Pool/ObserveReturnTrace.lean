import Benchmarks.UniswapV3.Pool.ObserveEncodeHeads

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observeReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw s t p : UInt256} {mem rdata : ByteArray}
    {xs ys : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1699⟩ (s :: t :: R) mem aw rdata σ k C)
    (hm : MemoryCursor mem aw p) (ht : DynamicWordArrayMemory mem t xs)
    (hs : DynamicWordArrayMemory mem s ys) (htlo : 96 ≤ t.toNat) (hslo : 96 ≤ s.toNat)
    (htend : t.toNat + 32 * (xs.length + 1) ≤ p.toNat)
    (hsend : s.toNat + 32 * (ys.length + 1) ≤ p.toNat)
    (hb : p.toNat + 128 + 32 * (xs.length + ys.length) ≤ 2 ^ 200)
    (hov : R.length + 20 ≤ 1024) :
    RDret (deployedRuntime v) g s0 σ (wordArrayBytes (observeEncodeWords xs ys)) := by
  have hp := hm.lower
  have hp96 := uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  have ht32 := uadd_word_ofNat_toNat t 32 (by change _ < 2 ^ 256; omega)
  have hs32 := uadd_word_ofNat_toNat s 32 (by change _ < 2 ^ 256; omega)
  have hpSec : (p + UInt256.ofNat (128 + 32 * xs.length)).toNat = p.toNat + 128 + 32 * xs.length := by
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)]; omega
  obtain ⟨aw1, k1, C1, ha1, r1⟩ := observeEncodeFirstHeadX (v := v) rd hm ht htend (by omega) (by omega)
  have pref1 : MemoryPrefix mem (observeEncodeFirstHead mem p xs.length) p.toNat :=
    (memoryPrefix_sparse_writeWord mem p.toNat p.toNat _ (Or.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ (p.toNat + 64) p.toNat _ (Or.inl (by omega)))
  have ht1 := MemoryPrefix.wordArray pref1 ht htlo (by
    simpa only [dynamicWordArrayWords, List.length_cons] using htend)
  have ht1tail : WordArrayMemory (observeEncodeFirstHead mem p xs.length)
      (t + UInt256.ofNat 32 + UInt256.ofNat (32 * 0)) xs := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
      using WordArrayMemory.tail ht1 (by change _ < 2 ^ 256; omega)
  obtain ⟨aw2, k2, C2, ha2, r2⟩ := observeCopyLoopX false (v := v) r1 ha1 (by omega) ht1tail
    (by rw [ht32, hp96]; omega) (by rw [hp96]; omega)
    (by dsimp only [List.length]; omega)
  simp only [hp96, Nat.mul_zero, Nat.add_zero] at r2
  change RD (deployedRuntime v) ee g s0 ⟨1767⟩
    (observeEncodeFirstStack xs.length xs.length s t p R)
    (observeEncodeFirstMem mem p xs) aw2 rdata σ k2 C2 at r2
  have hm2a := MemoryCursor.writeWord hm p.toNat (UInt256.ofNat 64) (by omega)
  have hm2b := MemoryCursor.writeWord hm2a (p.toNat + 64) (UInt256.ofNat xs.length) (by omega)
  have hm2c := MemoryCursor.writeWordArray hm2b (p.toNat + 96) xs (by omega)
  have hm2 : MemoryCursor (observeEncodeFirstMem mem p xs) aw2 p :=
    ⟨hm2c.size, hm2c.free, hm2c.lower, ha2⟩
  have hs2 := MemoryPrefix.wordArray (observeEncodeFirstPrefix mem p xs) hs hslo (by
    simpa only [dynamicWordArrayWords, List.length_cons] using hsend)
  obtain ⟨aw3, k3, C3, ha3, r3⟩ := observeEncodeSecondHeadX (v := v) r2 hm2 hs2 hsend
    (by omega) (by omega)
  have hs3 := MemoryPrefix.wordArray (observeEncodeSecondPrefix _ p xs.length ys.length) hs2 hslo
    (by simpa only [dynamicWordArrayWords, List.length_cons] using hsend)
  have hs3tail : WordArrayMemory
      (observeEncodeSecondHead (observeEncodeFirstMem mem p xs) p xs.length ys.length)
      (s + UInt256.ofNat 32 + UInt256.ofNat (32 * 0)) ys := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
      using WordArrayMemory.tail hs3 (by change _ < 2 ^ 256; omega)
  obtain ⟨aw4, k4, C4, _, r4⟩ := observeCopyLoopX true (v := v) r3 ha3 (by omega) hs3tail
    (by rw [hs32, hpSec]; omega) (by rw [hpSec]; omega)
    (by dsimp only [List.length]; omega)
  simp only [hpSec, Nat.mul_zero, Nat.add_zero] at r4
  change RD (deployedRuntime v) ee g s0 ⟨1830⟩
    (observeEncodeSecondStack ys.length xs.length ys.length s t p R)
    (observeEncodeMem mem p xs ys) aw4 rdata σ k4 C4 at r4
  have r5 := uniswapV3Pool_block_1830 (immWords := wordsOf (immStore v))
    (by omega) r4
  have hfree : memLoad (UInt256.ofNat 64) (observeEncodeMem mem p xs ys) = p :=
    (observeEncodeCursor hm xs ys).load64
  have he : UInt256.ofNat (32 * ys.length) + (p + UInt256.ofNat (128 + 32 * xs.length)) =
      p + UInt256.ofNat (128 + 32 * (xs.length + ys.length)) := by
    rw [u256_add_comm (UInt256.ofNat (32 * ys.length)), wordAddNat_assoc]
    congr 2
    omega
  rw [hfree, he, word_add_sub_left, ulit_toNat' (128 + 32 * (xs.length + ys.length))
    (by change _ < 2 ^ 256; omega)] at r5
  have hlen : 32 * (observeEncodeWords xs ys).length = 128 + 32 * (xs.length + ys.length) := by
    simp only [observeEncodeWords, List.length_append, List.length_cons, List.length_nil]
    omega
  have hbytes := (observeEncodeMemory mem p xs ys (by change _ < 2 ^ 256; omega)).bytes
    (by rw [hlen]; change _ < 2 ^ 256; omega)
  rw [hlen] at hbytes
  rwa [hbytes] at r5

end Benchmarks.UniswapV3.Pool
