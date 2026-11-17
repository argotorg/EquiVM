import Benchmarks.Dss.Dog.BarkDecodeToBody

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogCheckedMulReturns {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1010)
    (hret : (D_J code 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd4564 : RD code I g s0 ⟨4564⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD code I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
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
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd4591 := rd4591prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4558prep := evm_run rd4591 with [
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
    have rd4558 := rd4558prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4563 := evm_run rd4558 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4563.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
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
      hy0 (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
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
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd4558 := rd4558prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      heqCond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4563 := evm_run rd4558 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4563.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩


end Benchmarks.Dss.Dog
