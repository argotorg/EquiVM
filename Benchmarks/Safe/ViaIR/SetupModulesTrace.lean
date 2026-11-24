import Benchmarks.Safe.ViaIR.SetupModulesPrepare
import Benchmarks.Safe.ViaIR.ExecuteCallSource
import Benchmarks.Safe.ViaIR.RawDelegateCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSetupModulesTrace (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3409⟩
      (UInt256.ofNat ptr :: p.target :: p.target :: token :: receiver :: payment :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem ptr p.payload) (hp : 96 ≤ ptr)
    (hb : ptr + 64 + p.payload.size < UInt256.size)
    (hc : p.target.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecFuncBody fork config p.frame evm setupModulesFunction.body .reverted) ∨
    ∃ f' evm' out aw' k' C' x y,
      ExecFuncBody fork config p.frame evm setupModulesFunction.body (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨3475⟩ (x :: y :: token :: receiver :: payment :: ⟨0⟩ :: R)
        (setupModulesMemory mem) aw' out evm'.accountMap k' C' := by
  obtain ⟨hrev, hsource⟩ | ⟨aw₁, k₁, C₁, he, h₁⟩ :=
    safeSetupModulesPrepare p evm h hee hacc hperm (by omega)
  · exact .inl ⟨hrev, hsource⟩
  have hee₁ : (p.state evm).executionEnv = I := by
    simpa only [SetupModulesInput.state, writeModuleLink, storageStore_executionEnv] using hee
  have hw₁ : (p.state evm).σ₀ = s0.σ₀ := by
    simpa only [SetupModulesInput.state, writeModuleLink, storageStore_σ₀] using hworld
  by_cases ht : p.target = ⟨0⟩
  · simp only [if_pos ht] at h₁
    exact .inr ⟨p.frame, p.state evm, rdata, aw₁, k₁, C₁, p.target, UInt256.ofNat ptr,
      safeSetupModulesZero (hperm := by simpa only [hee] using hperm) p evm he ht, hee₁, hw₁, h₁⟩
  simp only [if_neg ht] at h₁
  by_cases hcode : extCodeSizeWord (p.state evm).accountMap p.target = ⟨0⟩
  · obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_3503_taken_packed (by simp; omega)
      (by rw [hcode]; decide) (by jump_dest) h₁
    exact .inl ⟨safeRuntime_block_3581 (by simp; omega) h₂,
      safeSetupModulesNoCode (hperm := by simpa only [hee] using hperm) p evm hc he ht hcode⟩
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_3503_fallthrough_packed (by simp; omega)
    (isZero_eq_zero_of_ne hcode) h₁
  have h₃ := safeRuntime_block_3511 (by simp; omega) h₂
  simp only [safeRuntime_block_3511_stack] at h₃
  have hm' : BytesMemory (setupModulesMemory mem) ptr p.payload :=
    (hm.scratch (by omega) (by omega) ⟨1⟩ ⟨1⟩).scratch (by omega) (by omega) ⟨1⟩ ⟨1⟩
  have hdata : (setupModulesMemory mem).readWithPadding
      (UInt256.ofNat ptr + UInt256.ofNat 32).toNat
      (memLoad (UInt256.ofNat ptr) (setupModulesMemory mem)).toNat = p.payload := by
    have hptr : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
      uadd_ofNat_toNat (by omega) (by decide) (by omega)
    rw [hm'.length, ulit_toNat' _ (by omega), hptr]
    exact hm'.payload
  obtain ⟨evm', σ', z, out, aw₄, k₄, C₄, hcall, hee', hacc', hw', h₄, _⟩ :=
    rawDelegateCallTraceFrom (p.state evm) h₃ hee₁ rfl hw₁ (by native_decide) (by simp; omega)
  rw [callOutputMem_zero] at h₄
  have hdelegate : delegateCallViaEVM fork (p.state evm)
      (EVM.address (AccountAddress.ofUInt256 p.target)) p.payload (z, evm', out) := by
    simpa only [addressOfAddress, hdata] using hcall
  have hcallee := safeExecuteDelegateSource (value := ⟨0⟩) (operation := ⟨1⟩)
    (txGas := UInt256.lnot ⟨0⟩) rfl hdelegate
  have hsource := safeSetupModulesCalled (fork := fork) (hperm := by simpa only [hee] using hperm) p evm hc he ht hcode
    (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hcallee)
  cases z with
  | false =>
      have h₅ := safeRuntime_block_3525_taken (by simp; omega) (by decide) (by jump_dest) h₄
      simp only [safeRuntime_block_3525_taken_stack] at h₅
      exact .inl ⟨safeRuntime_block_3536 (by simp; omega) h₅, hsource⟩
  | true =>
      have h₅ := safeRuntime_block_3525_fallthrough (by simp; omega) rfl h₄
      simp only [safeRuntime_block_3525_fallthrough_stack] at h₅
      have h₆ := safeRuntime_block_3530 (by simp; omega) (by jump_dest) h₅
      rw [← hacc'] at h₆
      exact .inr ⟨p.finalFrame true, evm', out, aw₄, _, _, ⟨0⟩, ⟨0⟩,
        hsource, hee', hw', h₆⟩

end Benchmarks.Safe.ViaIR
