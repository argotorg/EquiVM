import Benchmarks.UniswapV3.Pool.FullMathArithmetic
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
open scoped Fin.IntCast Fin.CommRing
set_option maxRecDepth 10000

def inverseNewtonWord (d i : UInt256) : Nat → UInt256
  | 0 => i
  | n + 1 => let x := inverseNewtonWord d i n; UInt256.mul (UInt256.sub ⟨2⟩ (UInt256.mul d x)) x

theorem inverseNewtonWord_val (d i : UInt256) (n : Nat) :
    (inverseNewtonWord d i n).val = inverseNewton d.val i.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [inverseNewtonWord, UInt256.mul, UInt256.sub, ih, inverseNewton]
    exact mul_comm _ _

theorem inverseNewtonWord_eq (d : UInt256) :
    inverseNewtonWord d (UInt256.xor ⟨2⟩ (UInt256.mul d ⟨3⟩)) 6 = wordInverse d := by
  rw [u256_mul_comm d]
  apply u256_inj
  exact congrArg Fin.val (inverseNewtonWord_val d (wordInverseSeed d) 6)

theorem fullMathLongX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret a b d : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13083⟩
      (productHigh a b :: UInt256.mul a b :: ⟨0⟩ :: d :: b :: a :: ret :: R)
      mem aw rdata σ k C)
    (hv : fullMathValid a b d)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (fullMathResult a b d :: R) mem aw rdata σ k' C' := by
  have r1 := uniswapV3Pool_block_13083 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  have htwos : UInt256.land d (UInt256.sub (UInt256.ofNat 0) d) = wordLowBit d :=
    u256_land_comm _ _
  have hr1 : RD (deployedRuntime v) ee g s0 ⟨13151⟩
      (UInt256.sub ⟨0⟩ (wordLowBit d) :: wordLowBit d ::
        inverseNewtonWord (UInt256.div d (wordLowBit d))
          (UInt256.xor ⟨2⟩ (UInt256.mul (UInt256.div d (wordLowBit d)) ⟨3⟩)) 6 ::
        UInt256.mulMod a b d :: ⟨0⟩ :: productHigh a b :: UInt256.mul a b :: ⟨0⟩ ::
        UInt256.div d (wordLowBit d) :: b :: a :: ret :: R)
      mem aw rdata σ (k + 64) (C + 223) := by
    simp only [uniswapV3Pool_block_13083_stack] at r1
    rw [htwos] at r1
    exact r1
  rw [inverseNewtonWord_eq] at hr1
  have r2 := uniswapV3Pool_block_13151 (immWords := wordsOf (immStore v)) (by evm_ov) hr1
  have hr2 : RD (deployedRuntime v) ee g s0 ⟨13186⟩
      (fullMathResult a b d :: UInt256.div d (wordLowBit d) :: b :: a :: ret :: R)
      mem aw rdata σ (k + 64 + 34) (C + 223 + 108) := by
    simp only [uniswapV3Pool_block_13151_stack] at r2
    change RD (deployedRuntime v) ee g s0 ⟨13186⟩
      (fullMathAlgorithm a b d :: UInt256.div d (wordLowBit d) :: b :: a :: ret :: R)
      mem aw rdata σ (k + 64 + 34) (C + 223 + 108) at r2
    rw [fullMathAlgorithm_eq a b d hv] at r2
    exact r2
  have r3 := uniswapV3Pool_block_13186 (immWords := wordsOf (immStore v)) (by evm_ov) hret hr2
  exact ⟨_, _, by omega, r3⟩

theorem fullMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret a b d : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13017⟩ (d :: b :: a :: ret :: R)
      mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    (¬ fullMathValid a b d ∧ RDrev (deployedRuntime v) g s0) ∨
    (fullMathValid a b d ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (fullMathResult a b d :: R) mem aw rdata σ k' C') := by
  have hhigh : UInt256.sub
      (UInt256.sub (UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))) (UInt256.mul b a))
      (UInt256.lt (UInt256.mulMod a b (UInt256.lnot (UInt256.ofNat 0))) (UInt256.mul b a)) =
      productHigh a b := by rw [u256_mul_comm b a]; rfl
  by_cases hz : productHigh a b = ⟨0⟩
  · have r1 := uniswapV3Pool_block_13017_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hhigh]; exact hz) rd
    have r1' : RD (deployedRuntime v) ee g s0 ⟨13048⟩
        (productHigh a b :: UInt256.mul a b :: ⟨0⟩ :: d :: b :: a :: ret :: R)
        mem aw rdata σ (k + 27) (C + 91) := by
      simpa only [uniswapV3Pool_block_13017_fallthrough_stack, hhigh, u256_mul_comm b a] using r1
    by_cases hd : 0 < d.toNat
    · have hv : fullMathValid a b d := by
        change fullMathProduct a b / UInt256.size < d.toNat
        rw [← productHigh_toNat, hz]
        exact hd
      have r2 := uniswapV3Pool_block_13048_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_one (a := d) (b := UInt256.ofNat 0) hd]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1'
      have r3 := uniswapV3Pool_block_13060 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      have r3' : RD (deployedRuntime v) ee g s0 ⟨13186⟩
          (fullMathResult a b d :: d :: b :: a :: ret :: R)
          mem aw rdata σ (k + 27 + 5 + 9) (C + 91 + 22 + 30) := by
        simpa only [uniswapV3Pool_block_13060_stack, fullMath_small_eq a b d hv hz] using r3
      have r4 := uniswapV3Pool_block_13186 (immWords := wordsOf (immStore v))
        (by evm_ov) hret r3'
      exact Or.inr ⟨hv, _, _, by omega, r4⟩
    · have hv : ¬ fullMathValid a b d := fun h ↦ hd (fullMath_denominator_pos h)
      have r2 := uniswapV3Pool_block_13048_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_zero (by exact Nat.le_of_not_gt hd)]; rfl) r1'
      exact Or.inl ⟨hv, uniswapV3Pool_block_13056 (immWords := wordsOf (immStore v)) (by evm_ov) r2⟩
  · have r1 := uniswapV3Pool_block_13017_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hhigh]; exact hz)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1' : RD (deployedRuntime v) ee g s0 ⟨13071⟩
        (productHigh a b :: UInt256.mul a b :: ⟨0⟩ :: d :: b :: a :: ret :: R)
        mem aw rdata σ (k + 27) (C + 91) := by
      simpa only [uniswapV3Pool_block_13017_taken_stack, hhigh, u256_mul_comm b a] using r1
    by_cases hv : fullMathValid a b d
    · have r2 := uniswapV3Pool_block_13071_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_one (by rw [productHigh_toNat]; exact hv)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1'
      obtain ⟨k', C', hC, r3⟩ := fullMathLongX (v := v) r2 hv hret hov
      exact Or.inr ⟨hv, k', C', by omega, r3⟩
    · have r2 := uniswapV3Pool_block_13071_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [ugt_zero (by rw [productHigh_toNat]; exact Nat.le_of_not_gt hv)]; rfl) r1'
      exact Or.inl ⟨hv, uniswapV3Pool_block_13079 (immWords := wordsOf (immStore v)) (by evm_ov) r2⟩

end Benchmarks.UniswapV3.Pool
