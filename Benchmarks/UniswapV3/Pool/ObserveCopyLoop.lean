import Benchmarks.UniswapV3.Pool.WordArrayBytes
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_009
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observeCopyLoopX (second : Bool) {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C i n : Nat} {aw src dest : UInt256} {mem rdata : ByteArray}
    {ws : List UInt256} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 (if second then ⟨1806⟩ else ⟨1743⟩)
      (UInt256.ofNat (32 * i) :: src :: dest :: UInt256.ofNat (32 * n) :: R)
      mem aw rdata σ k C)
    (ha : ActiveWords aw) (hn : i + ws.length = n)
    (hm : WordArrayMemory mem (src + UInt256.ofNat (32 * i)) ws)
    (hdisj : src.toNat + 32 * n ≤ dest.toNat) (hb : dest.toNat + 32 * n ≤ 2 ^ 200)
    (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', ActiveWords aw' ∧
      RD (deployedRuntime v) ee g s0 (if second then ⟨1830⟩ else ⟨1767⟩)
        (UInt256.ofNat (32 * n) :: src :: dest :: UInt256.ofNat (32 * n) :: R)
        (writeWordArray mem (dest.toNat + 32 * i) ws) aw' rdata σ k' C' := by
  induction ws generalizing i mem aw k C with
  | nil =>
      have hi : i = n := by simpa only [List.length_nil, Nat.add_zero] using hn
      subst i
      have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * n))
          (UInt256.ofNat (32 * n))) ≠ UInt256.ofNat 0 := by
        rw [ult_zero (Nat.le_refl _)]; decide
      refine ⟨aw, k + 7, C + 26, ha, ?_⟩
      cases second
      · exact uniswapV3Pool_block_1743_taken (immWords := wordsOf (immStore v)) (by omega) hcond
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      · exact uniswapV3Pool_block_1806_taken (immWords := wordsOf (immStore v)) (by omega) hcond
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  | cons w ws ih =>
      have hi : i < n := by simp only [List.length_cons] at hn; omega
      have hni : i + 1 + ws.length = n := by simp only [List.length_cons] at hn; omega
      have hword : ∀ j, j ≤ n → (UInt256.ofNat (32 * j)).toNat = 32 * j := by
        intro j hj; exact ulit_toNat' _ (by change _ < 2 ^ 256; omega)
      have hsrc : ∀ j, j ≤ n → (src + UInt256.ofNat (32 * j)).toNat = src.toNat + 32 * j := by
        intro j hj; exact uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
      have hdest : (dest + UInt256.ofNat (32 * i)).toNat = dest.toNat + 32 * i :=
        uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
      have hbs : (src + UInt256.ofNat (32 * i)).toNat + 32 ≤ 2 ^ 200 := by
        rw [hsrc i (by omega)]; omega
      have hbd : (dest + UInt256.ofNat (32 * i)).toNat + 32 ≤ 2 ^ 200 := by rw [hdest]; omega
      have hload : memLoad (src + UInt256.ofNat (32 * i)) mem = w := by
        apply mloadWordValue_of_readWithPadding
        · have hs := hm.size; simp only [List.length_cons] at hs; omega
        · simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using hm.read 0 (by simp)
      have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat (32 * i))
          (UInt256.ofNat (32 * n))) = UInt256.ofNat 0 := by
        rw [ult_one (by rw [hword i (by omega), hword n (le_refl _)]; omega)]
        rfl
      have r1 : RD (deployedRuntime v) ee g s0 (if second then ⟨1815⟩ else ⟨1752⟩)
          (UInt256.ofNat (32 * i) :: src :: dest :: UInt256.ofNat (32 * n) :: R)
          mem aw rdata σ (k + 7) (C + 26) := by
        cases second
        · exact uniswapV3Pool_block_1743_fallthrough (immWords := wordsOf (immStore v)) (by omega) hcond rd
        · exact uniswapV3Pool_block_1806_fallthrough (immWords := wordsOf (immStore v)) (by omega) hcond rd
      have hinc : UInt256.ofNat 32 + UInt256.ofNat (32 * i) = UInt256.ofNat (32 * (i + 1)) := by
        apply u256_inj
        rw [uadd_toNat, hword i (by omega), hword (i + 1) (by omega)]
        change (32 + 32 * i) % UInt256.size = _
        rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
        omega
      have r2 : ∃ k' C', RD (deployedRuntime v) ee g s0 (if second then ⟨1806⟩ else ⟨1743⟩)
          (UInt256.ofNat (32 * (i + 1)) :: src :: dest :: UInt256.ofNat (32 * n) :: R)
          (writeWord mem (dest.toNat + 32 * i) w)
          (M (M aw (src + UInt256.ofNat (32 * i)) ⟨32⟩) (dest + UInt256.ofNat (32 * i)) ⟨32⟩)
          rdata σ k' C' := by
        cases second
        · have h := uniswapV3Pool_block_1752 (immWords := wordsOf (immStore v))
            (by dsimp only [List.length]; omega)
            (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
          simp only [uniswapV3Pool_block_1752_stack, uniswapV3Pool_block_1752_memory, hload,
            hinc, u256_add_comm (UInt256.ofNat (32 * i)), hdest] at h
          exact ⟨_, _, h⟩
        · have h := uniswapV3Pool_block_1815 (immWords := wordsOf (immStore v))
            (by dsimp only [List.length]; omega)
            (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
          simp only [uniswapV3Pool_block_1815_stack, uniswapV3Pool_block_1815_memory, hload,
            hinc, u256_add_comm (UInt256.ofNat (32 * i)), hdest] at h
          exact ⟨_, _, h⟩
      obtain ⟨k2, C2, r2⟩ := r2
      have he : (src + UInt256.ofNat (32 * i)) + UInt256.ofNat 32 =
          src + UInt256.ofNat (32 * (i + 1)) := by
        apply u256_inj
        rw [uadd_word_ofNat_toNat _ 32 (by change _ < 2 ^ 256; omega),
          hsrc i (by omega), hsrc (i + 1) (by omega)]
        omega
      have ht := hm.tail (by change _ < 2 ^ 256; omega)
      rw [he] at ht
      have hm2 := ht.write_disjoint (dest.toNat + 32 * i) w (Or.inr (by
        rw [hsrc (i + 1) (by omega)]; omega))
      obtain ⟨aw3, k3, C3, ha3, r3⟩ := ih r2 (activeWords_expand32 (activeWords_expand32 ha hbs) hbd)
        hni hm2
      refine ⟨aw3, k3, C3, ha3, ?_⟩
      simpa only [writeWordArray, show dest.toNat + 32 * (i + 1) = dest.toNat + 32 * i + 32 by omega]
        using r3

end Benchmarks.UniswapV3.Pool
