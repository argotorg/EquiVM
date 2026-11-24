import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Runtime_029
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

-- The generated SLOAD summary hides its gas counter. Preserve a lower bound for long loops.
theorem safeStorageAtBodyCost {I g s0 σ k C aw mem rdata}
    {index offset len ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6194⟩ (index :: offset :: len :: ptr :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', C + 32 ≤ C' ∧ RD fork safeBytecode I g s0 ⟨6165⟩
      ((index + UInt256.ofNat 1) :: offset :: len :: ptr :: R)
      (safeRuntime_block_6194_memory (ee := I) (mem := mem) (σ := σ) (x0 := index)
        (x1 := offset) (x3 := ptr))
      (M aw ((ptr + UInt256.shiftLeft index (UInt256.ofNat 5)) + UInt256.ofNat 32) ⟨32⟩)
      rdata σ k' C' := by
  have r1 := h.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcost, r7⟩ := RD.sloadMono r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup8 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 6165) (by native_decide) (by evm_ov)
  have hfinal := r17.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, hfinal⟩

theorem safeStorageAtStepCost {I g s0 σ k C aw mem rdata}
    {offset len ptr : UInt256} {index : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6165⟩
      (UInt256.ofNat index :: offset :: len :: ptr :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hi : index < len.toNat) :
    ∃ mem' aw' k' C', C + 32 ≤ C' ∧ RD fork safeBytecode I g s0 ⟨6165⟩
      (UInt256.ofNat (index + 1) :: offset :: len :: ptr :: R)
      mem' aw' rdata σ k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat index) len = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' index (lt_trans hi len.val.isLt)]; exact hi)
  have hd := safeRuntime_block_6165_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h
  obtain ⟨k', C', hcost, hr⟩ := safeStorageAtBodyCost hd hov
  have he : UInt256.ofNat index + UInt256.ofNat 1 = UInt256.ofNat (index + 1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat index
  rw [he] at hr
  exact ⟨_, _, k', C', by omega, hr⟩

theorem safeStorageAtGasLoop {I g s0 σ k C aw mem rdata}
    {offset len ptr : UInt256} {index fuel : Nat} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6165⟩
      (UInt256.ofNat index :: offset :: len :: ptr :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hi : index + fuel ≤ len.toNat) :
    ∃ mem' aw' k' C', C + 32 * fuel ≤ C' ∧ RD fork safeBytecode I g s0 ⟨6165⟩
      (UInt256.ofNat (index + fuel) :: offset :: len :: ptr :: R)
      mem' aw' rdata σ k' C' := by
  induction fuel generalizing index k C aw mem with
  | zero => exact ⟨mem, aw, k, C, by omega, by simpa using h⟩
  | succ fuel ih =>
      obtain ⟨mem₁, aw₁, k₁, C₁, hc₁, h₁⟩ := safeStorageAtStepCost h hov (by omega)
      obtain ⟨mem₂, aw₂, k₂, C₂, hc₂, h₂⟩ := ih h₁ (by omega)
      exact ⟨mem₂, aw₂, k₂, C₂, by omega,
        by simpa only [show index + 1 + fuel = index + (fuel + 1) by omega] using h₂⟩

theorem safeStorageAtHugeOOG {I g s0 σ k C aw mem rdata}
    {offset len ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6165⟩ (⟨0⟩ :: offset :: len :: ptr :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hl : 2 ^ 251 ≤ len.toNat) :
    X fork (g.toNat + 1) (D_J safeBytecode 0) s0 = .error .OutOfGass := by
  obtain ⟨_, _, _, C', hc, hr⟩ := safeStorageAtGasLoop (fuel := 2 ^ 251) h hov hl
  have hg : g.toNat < 2 ^ 256 := g.isLt
  exact RD.oog_of_cost_gt hr (by norm_num at hc; omega)

end Benchmarks.Safe.ViaIR
