import Benchmarks.Morpho.MorphoBlue.Dispatch
import Benchmarks.Morpho.MorphoBlue.BodyCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: the unsigned subtraction check used by the via-IR compiler.
theorem checkedSubGuard_ok (a b : UInt256) (h : b.toNat ≤ a.toNat) :
    UInt256.gt (UInt256.sub a b) a = ⟨0⟩ := by
  apply ugt_zero
  rw [usub_toNat h]
  exact Nat.sub_le _ _

theorem checkedSubGuard_underflow (a b : UInt256) (h : a.toNat < b.toNat) :
    UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
  apply ugt_one
  rw [usub_toNat_underflow h]
  have hb := b.val.isLt
  change b.toNat < UInt256.size at hb
  omega

-- LIBRARY CANDIDATE: the via-IR unsigned multiplication overflow predicate.
def checkedMulGuard (a b : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul a b) a) b)
    (UInt256.isZero a))

theorem checkedMulGuard_ok (a b : UInt256) (h : a.toNat * b.toNat < UInt256.size) :
    checkedMulGuard a b = ⟨0⟩ := by
  unfold checkedMulGuard
  by_cases ha : a = ⟨0⟩
  · rw [ha, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from rfl]
    exact isZero_eq_zero_of_ne (u256_lor_one_right_ne_zero _)
  · have hm : UInt256.div (UInt256.mul a b) a = b := by
      rw [u256_mul_comm]
      exact u256_mul_div_right_eq_of_noOverflow b a ha (by simpa only [Nat.mul_comm] using h)
    rw [hm, uInt256_eq_self, isZero_eq_zero_of_ne ha]
    decide

theorem checkedMulGuard_overflow (a b : UInt256) (h : UInt256.size ≤ a.toNat * b.toNat) :
    checkedMulGuard a b = ⟨1⟩ := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at h
    change UInt256.size ≤ 0 * b.toNat at h
    norm_num [UInt256.size] at h
  have hm : UInt256.div (UInt256.mul a b) a ≠ b := by
    rw [u256_mul_comm]
    exact checkedMul_div_ne (by simpa only [Nat.mul_comm] using h)
  rw [checkedMulGuard, show UInt256.eq (UInt256.div (UInt256.mul a b) a) b = ⟨0⟩ by
    simp only [UInt256.eq, decide_eq_false hm]; rfl, isZero_eq_zero_of_ne ha]
  decide

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {a b ret : UInt256} {R : List UInt256}

theorem morphoCheckedSubOk (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hfit : b.toNat ≤ a.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12833) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_12833_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (checkedSubGuard_ok a b hfit) h
  exact ⟨_, _, morphoBlocks.morpho_block_12845 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1⟩

theorem morphoCheckedSubReverts (hstack : R.length + 6 ≤ 1024) (hunder : a.toNat < b.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12833) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_12833_taken (immWords := wordsOf (immStore v))
    (by omega) (by rw [checkedSubGuard_underflow a b hunder]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_12833_taken_stack, List.length_cons]; omega) rd1

theorem morphoCheckedAddOk (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hc := checkedAddNoOverflowGt a b hfit
  rw [u256_add_comm b a] at hc
  have rd1 := morphoBlocks.morpho_block_12651_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hc h
  exact ⟨_, _, morphoBlocks.morpho_block_12663 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1⟩

theorem morphoCheckedAddReverts (hstack : R.length + 6 ≤ 1024)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have hc := checkedAddOverflowGt a b hover
  rw [u256_add_comm b a] at hc
  have rd1 := morphoBlocks.morpho_block_12651_taken (immWords := wordsOf (immStore v))
    (by omega) (by rw [hc]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_12651_taken_stack, List.length_cons]; omega) rd1

theorem morphoCheckedMulOk (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_14395_fallthrough (immWords := wordsOf (immStore v))
    hstack (checkedMulGuard_ok a b hfit) h
  exact ⟨_, _, morphoBlocks.morpho_block_14413 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1⟩

theorem morphoCheckedMulReverts (hstack : R.length + 6 ≤ 1024)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_14395_taken (immWords := wordsOf (immStore v))
    hstack (by change checkedMulGuard a b ≠ _; rw [checkedMulGuard_overflow a b hover]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3277 (immWords := wordsOf (immStore v))
    (by simp only [morphoBlocks.morpho_block_14395_taken_stack, List.length_cons]; omega) rd1

theorem morphoCheckedDivOk (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true) (hb : b ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14414) (a :: b :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.div a b :: R) mem aw rdata σ k' C' := by
  have rd1 := morphoBlocks.morpho_block_14414_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hb) h
  exact ⟨_, _, morphoBlocks.morpho_block_14421 (immWords := wordsOf (immStore v))
    (by omega) hvalid rd1⟩

theorem morphoCheckedDivReverts (hstack : R.length + 6 ≤ 1024) (hb : b = ⟨0⟩)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14414) (a :: b :: ret :: R)
      mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  have rd1 := morphoBlocks.morpho_block_14414_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hb]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoBlocks.morpho_block_3572 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
