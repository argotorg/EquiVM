import Benchmarks.Dss.Dog.BarkCheckedMulOverflow

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogCheckedAddReturns {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1015)
    (hfit : x.toNat + y.toNat < UInt256.size)
    (rd4625 : RD code I g s0 ⟨4625⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J code 0).contains ret = true) :
    ∃ k' C', RD code I g s0 ret ((x + y) :: R) mem aw rdata acc k' C' := by
  have hwf : solcCheckedAddSuccessWf code ⟨4625⟩ ⟨4558⟩ := by
    dsimp [solcCheckedAddSuccessWf]
    repeat' first | apply And.intro |
      (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
       native_decide)
  exact RD.solcCheckedAddSuccess rd4625 hwf hfit hret
    (dogPatchedJumpDest hpatch (by native_decide)) (by omega)

theorem RD.dogCheckedAddOverflowReverts {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1015)
    (hover : UInt256.size ≤ x.toNat + y.toNat)
    (rd4625 : RD code I g s0 ⟨4625⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev code g s0 := by
  have hsumLt2 : x.toNat + y.toNat < 2 * UInt256.size := by
    have hx : x.toNat < UInt256.size := x.val.isLt
    have hy : y.toNat < UInt256.size := y.val.isLt
    omega
  have hmod : (x.toNat + y.toNat) % UInt256.size =
      x.toNat + y.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (x + y).toNat = x.toNat + y.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (x + y) x = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hy : y.toNat < UInt256.size := y.val.isLt
    omega
  have rd4632pre := evm_run rd4625 with [
    raw jumpdest
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
    raw add
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
      (by evm_ov)]
  have rd4632₀ := evm_run rd4632pre with [
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4632 := rd4632₀
  rw [hlt] at rd4632
  have rd4633₀ := evm_run rd4632 with [
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4633 := rd4633₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4633
  have rd4636 := evm_run rd4633 with [
    raw push2 ⟨4558⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4637 := rd4636.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact RD.solcPush1Dup1Revert0 rd4637
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
