import Benchmarks.Dss.Dog.BarkMinReturns

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogCheckedMulOverflowReverts {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd4564 : RD code I g s0 ⟨4564⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev code g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd4591prep := evm_run rd4564 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4591⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd4574 := rd4591prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (by evm_ov)
  have rd4586 := evm_run rd4574 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mul
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4588⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4588 := rd4586.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hyNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd4558prep := evm_run rd4588 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw eq
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4558⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rdFallthrough := rd4558prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    heqCond (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)


end Benchmarks.Dss.Dog
