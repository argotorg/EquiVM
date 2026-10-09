import Benchmarks.Morpho.MorphoBlue.MulDivUpSource
import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the literal all-ones word is the modular negative of one.
theorem wordAddNegOne (x : UInt256) :
    x + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 =
      UInt256.sub x (UInt256.ofNat 1) := by
  exact u256_add_lnot_zero_eq_sub_one x

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap} {k C : Nat}
  {x y d ret : UInt256} {R : List UInt256}

theorem morphoMulDivUpReachDenom (hstack : R.length + 12 ≤ 1024)
    (hf : x.toNat * y.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14424) (x :: y :: d :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14434)
      (UInt256.mul x y :: d :: ret :: R) mem aw out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_14424 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoCheckedMulOk (v := v) (by simp; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1

theorem morphoMulDivUpReachAdd (hstack : R.length + 12 ≤ 1024) (hn : 1 ≤ d.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14434)
      (UInt256.mul x y :: d :: ret :: R) mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([UInt256.mul x y, UInt256.sub d (UInt256.ofNat 1), UInt256.ofNat 2004, d,
        UInt256.ofNat 14109, ret] ++ R) mem aw out σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_14434_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [wordAddNegOne]; exact checkedSubGuard_ok _ _ hn) h
  dsimp only [morphoBlocks.morpho_block_14434_fallthrough_stack] at rd1
  rw [wordAddNegOne] at rd1
  exact ⟨_, _, morphoBlocks.morpho_block_14479 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1⟩

theorem morphoMulDivUpOk (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hf : MulDivUpFits x y d)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14424) (x :: y :: d :: ret :: R)
      mem aw out σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (mulDivUpWord x y d :: R) mem aw out σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoMulDivUpReachDenom (v := v) hstack hf.1 h
  obtain ⟨k2, C2, rd2⟩ := morphoMulDivUpReachAdd (v := v) hstack hf.2.1 rd1
  obtain ⟨k3, C3, rd3⟩ := morphoCheckedAddOk (v := v) (by simp; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hf.2.2 rd2
  have rd4 := morphoBlocks.morpho_block_2004 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd3
  obtain ⟨k5, C5, rd5⟩ := morphoCheckedDivOk (v := v) (by simp; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (fun hz ↦ by have hn := hf.2.1; rw [hz] at hn; contradiction) rd4
  exact ⟨_, _, morphoBlocks.morpho_block_14109 (immWords := wordsOf (immStore v)) (by simp; omega) hvalid rd5⟩

theorem morphoMulDivUpReverts (hstack : R.length + 12 ≤ 1024) (hf : ¬ MulDivUpFits x y d)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14424) (x :: y :: d :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hp : x.toNat * y.toNat < UInt256.size
  swap
  · have rd1 := morphoBlocks.morpho_block_14424 (immWords := wordsOf (immStore v))
      (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoCheckedMulReverts (v := v) (by simp; omega) (Nat.le_of_not_gt hp) rd1
  obtain ⟨k1, C1, rd1⟩ := morphoMulDivUpReachDenom (v := v) hstack hp h
  by_cases hn : 1 ≤ d.toNat
  swap
  · have rd2 := morphoBlocks.morpho_block_14434_taken (immWords := wordsOf (immStore v))
      (by simp; omega)
      (by rw [wordAddNegOne, checkedSubGuard_underflow d (UInt256.ofNat 1) (by change d.toNat < 1; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega) rd2
  obtain ⟨k2, C2, rd2⟩ := morphoMulDivUpReachAdd (v := v) hstack hn rd1
  exact morphoCheckedAddReverts (v := v) (by simp; omega)
    (Nat.le_of_not_gt (fun ha ↦ hf ⟨hp, hn, ha⟩)) rd2

end Routines
end Benchmarks.Morpho.MorphoBlue
