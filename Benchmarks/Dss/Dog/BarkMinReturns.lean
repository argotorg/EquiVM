import Benchmarks.Dss.Dog.BarkCheckedMulReturns

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogMinReturns {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hret : (D_J code 0).contains ret = true)
    (rd4600 : RD code I g s0 ⟨4600⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ret
      ((if x.toNat ≤ y.toNat then x else y) :: R) mem aw rdata acc k' C' := by
  have rd4610prep := evm_run rd4600 with [
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
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4616⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  by_cases hle : x.toNat ≤ y.toNat
  · have hgt : UInt256.gt x y = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero hle
    have rd4610 := rd4610prep
    rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4610
    have rd4616 := rd4610.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4624 := evm_run rd4616 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap4
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
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
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4624.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hle] using rdret⟩
  · have hylt : y.toNat < x.toNat := by omega
    have hgt : UInt256.gt x y = ⟨1⟩ :=
      Reasoning.Theory.ugt_one hylt
    have rd4610 := rd4610prep
    rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4610
    have rd4611 := rd4610.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have rd4615 := evm_run rd4611 with [
      raw dup2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨4618⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd4618 := rd4615.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4624 := evm_run rd4618 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap4
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
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
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4624.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hle] using rdret⟩


end Benchmarks.Dss.Dog
