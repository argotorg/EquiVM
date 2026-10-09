import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_018
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

-- The generated SLOAD summary hides its gas counter. Preserve a lower bound for long loops.
theorem safeStorageAtBodyCost {I g s0 σ k C aw mem rdata}
    {index ptr scratch len offset : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3140⟩ (index :: ptr :: scratch :: len :: offset :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', C + 32 ≤ C' ∧ RD safeBytecode I g s0 ⟨3131⟩
      ((UInt256.ofNat 1 + index) :: ptr :: scratch :: len :: offset :: R)
      (safeRuntime_block_3140_memory (ee := I) (mem := mem) (σ := σ) (x0 := index)
        (x1 := ptr) (x4 := offset))
      (M aw ((ptr + UInt256.mul index (UInt256.ofNat 32)) + UInt256.ofNat 32) ⟨32⟩)
      rdata σ k' C' := by
  have h1 := h.dup5 (by native_decide) (by evm_ov)
  have h2 := h1.dup2 (by native_decide) (by evm_ov)
  have h3 := h2.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hcost, h4⟩ := RD.sloadMono h3 (by native_decide) (by evm_ov)
  have h5 := h4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have h6 := h5.dup1 (by native_decide) (by evm_ov)
  have h7 := h6.dup4 (by native_decide) (by evm_ov)
  have h8 := h7.mul (by native_decide) (by evm_ov)
  have h9 := h8.dup5 (by native_decide) (by evm_ov)
  have h10 := h9.add (by native_decide) (by evm_ov)
  have h11 := h10.add (by native_decide) (by evm_ov)
  have h12 := RD.genMstore h11 (by native_decide) (by evm_ov)
  have h13 := h12.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have h14 := h13.add (by native_decide) (by evm_ov)
  have h15 := h14.push2 (UInt256.ofNat 3131) (by native_decide) (by evm_ov)
  have h16 := h15.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by omega, h16⟩

theorem safeStorageAtStepCost {I g s0 σ k C aw mem rdata}
    {ptr scratch len offset : UInt256} {index : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3131⟩
      (UInt256.ofNat index :: ptr :: scratch :: len :: offset :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hi : index < len.toNat) :
    ∃ mem' aw' k' C', C + 32 ≤ C' ∧ RD safeBytecode I g s0 ⟨3131⟩
      (UInt256.ofNat (index + 1) :: ptr :: scratch :: len :: offset :: R)
      mem' aw' rdata σ k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat index) len = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' index (lt_trans hi len.val.isLt)]; exact hi)
  have hd := safeRuntime_block_3131_fallthrough (by simp; omega)
    (by rw [hlt]; decide) h
  obtain ⟨k', C', hcost, hr⟩ := safeStorageAtBodyCost hd hov
  have he : UInt256.ofNat 1 + UInt256.ofNat index = UInt256.ofNat (index + 1) :=
    u256_one_add_ofNat index
  rw [he] at hr
  exact ⟨_, _, k', C', by omega, hr⟩

theorem safeStorageAtGasLoop {I g s0 σ k C aw mem rdata}
    {ptr scratch len offset : UInt256} {index fuel : Nat} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3131⟩
      (UInt256.ofNat index :: ptr :: scratch :: len :: offset :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hi : index + fuel ≤ len.toNat) :
    ∃ mem' aw' k' C', C + 32 * fuel ≤ C' ∧ RD safeBytecode I g s0 ⟨3131⟩
      (UInt256.ofNat (index + fuel) :: ptr :: scratch :: len :: offset :: R)
      mem' aw' rdata σ k' C' := by
  induction fuel generalizing index k C aw mem with
  | zero => exact ⟨mem, aw, k, C, by omega, by simpa using h⟩
  | succ fuel ih =>
      obtain ⟨mem₁, aw₁, k₁, C₁, hc₁, h₁⟩ := safeStorageAtStepCost h hov (by omega)
      obtain ⟨mem₂, aw₂, k₂, C₂, hc₂, h₂⟩ := ih h₁ (by omega)
      exact ⟨mem₂, aw₂, k₂, C₂, by omega,
        by simpa only [show index + 1 + fuel = index + (fuel + 1) by omega] using h₂⟩

theorem safeStorageAtHugeOOG {I g s0 σ k C aw mem rdata}
    {ptr scratch len offset : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3131⟩ (⟨0⟩ :: ptr :: scratch :: len :: offset :: R)
      mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hl : 2 ^ 251 ≤ len.toNat) :
    X (g.toNat + 1) (D_J safeBytecode 0) s0 = .error .OutOfGass := by
  obtain ⟨_, _, _, C', hc, hr⟩ := safeStorageAtGasLoop (fuel := 2 ^ 251) h hov hl
  have hg : g.toNat < 2 ^ 256 := g.isLt
  exact RD.oog_of_cost_gt hr (by norm_num at hc; omega)

end Benchmarks.Safe
