import Benchmarks.Safe.SetupModulesPrepare
import Benchmarks.Safe.ExecuteRawTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupModulesTrace (p : SetupModulesInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8319⟩
      (UInt256.ofNat ptr :: p.target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem ptr p.payload) (hp : 96 ≤ ptr)
    (hb : ptr + 64 + p.payload.size < UInt256.size)
    (hc : p.target.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm setupModulesFunction.body .reverted) ∨
    ∃ f' evm' out aw' k' C',
      ExecFuncBody config p.frame evm setupModulesFunction.body (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret R (setupModulesMemory mem) aw' out evm'.accountMap k' C' := by
  obtain ⟨hrev, hsource⟩ | ⟨aw₁, k₁, C₁, he, h₁⟩ :=
    safeSetupModulesPrepare p evm h hee hacc hc hperm hov
  · exact .inl ⟨hrev, hsource⟩
  have hee₁ : (p.state evm).executionEnv = I := by
    simpa only [SetupModulesInput.state, writeModuleLink, storageStore_executionEnv] using hee
  have hw₁ : (p.state evm).σ₀ = s0.σ₀ := by
    simpa only [SetupModulesInput.state, writeModuleLink, storageStore_σ₀] using hworld
  by_cases ht : p.target = ⟨0⟩
  · simp only [if_pos ht] at h₁
    have h₂ := safeRuntime_block_1936 (by omega) hret h₁
    exact .inr ⟨p.frame, p.state evm, rdata, aw₁, _, _, safeSetupModulesZero p evm he ht,
      hee₁, hw₁, h₂⟩
  simp only [if_neg ht] at h₁
  by_cases hcode : extCodeSizeWord (p.state evm).accountMap p.target = ⟨0⟩
  · obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_8470_fallthrough_packed (by simp; omega) hcode h₁
    have h₃ := safeRuntime_block_8476 (by simp; omega) (by jump_dest) h₂
    exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₃,
      safeSetupModulesNoCode p evm hc he ht hcode⟩
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_8470_taken_packed (by simp; omega) hcode
    (by jump_dest) h₁
  have h₃ := safeRuntime_block_8492 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_8492_stack] at h₃
  have hm' : BytesMemory (setupModulesMemory mem) ptr p.payload :=
    (hm.scratch (by omega) (by omega) ⟨1⟩ ⟨1⟩).scratch (by omega) (by omega) ⟨1⟩ ⟨1⟩
  have hdata : (setupModulesMemory mem).readWithPadding
      (UInt256.ofNat ptr + UInt256.ofNat 32).toNat
      (memLoad (UInt256.ofNat ptr) (setupModulesMemory mem)).toNat = p.payload := by
    have hptr : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
      uadd_ofNat_toNat (by omega) (by decide) (by omega)
    rw [hm'.length, ulit_toNat' _ (by omega), hptr]
    exact hm'.payload
  obtain ⟨_, hn, _, _⟩ | ⟨evm', σ', z, out, aw₄, k₄, C₄, hcall, hee', hacc', hw', h₄, _, _⟩ :=
    safeExecuteRawTrace (p.state evm) p.payload h₃ hee₁ rfl hw₁ hdata (by decide)
      (by simp; omega) (by jump_dest)
  · exact False.elim (hn rfl)
  have hdelegate : delegateCallViaEVM (p.state evm)
      (EVM.address (AccountAddress.ofUInt256 p.target)) p.payload (z, evm', out) := by
    rcases hcall with ⟨_, hcall⟩ | ⟨hn, _⟩
    · exact hcall
    · exact False.elim (hn rfl)
  have hcallee := safeExecuteDelegateSource (value := ⟨0⟩) (operation := ⟨1⟩)
    (txGas := UInt256.lnot ⟨0⟩) rfl hdelegate
  have hsource := safeSetupModulesCalled p evm hc he ht hcode
    (by simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using hcallee)
  cases z with
  | false =>
      have h₅ := safeRuntime_block_8507_fallthrough (by simp; omega) rfl h₄
      simp only [safeRuntime_block_8507_fallthrough_stack] at h₅
      have h₆ := safeRuntime_block_8512 (by simp; omega) (by jump_dest) h₅
      exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₆, hsource⟩
  | true =>
      have h₅ := safeRuntime_block_8507_taken (by simp; omega) (by decide) (by jump_dest) h₄
      simp only [safeRuntime_block_8507_taken_stack] at h₅
      have h₆ := safeRuntime_block_1936 (by omega) hret h₅
      rw [← hacc'] at h₆
      exact .inr ⟨p.finalFrame true, evm', out, aw₄, _, _, hsource, hee', hw', h₆⟩

theorem safeInternalSetupModules {caller : Frame} {evm : EVM.State}
    {target payload : Expr} {retVar : Ident} {p : SetupModulesInput} {result : ExecResult}
    (hc : caller.contract = contract) (him : caller.immutables = ∅)
    (ht : evalExpr? config caller evm target = .ok (.address (AccountAddress.ofNat p.target.toNat)))
    (hd : evalExpr? config caller evm payload = .ok (.bytes p.payload))
    (hb : ExecFuncBody config p.frame evm setupModulesFunction.body result) :
    ExecStmt config caller evm (.internalCall "setupModules" [target, payload] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := setupModulesFunction) (locals := p.args)
    (argVals := [.address (AccountAddress.ofNat p.target.toNat), .bytes p.payload])
  · simp only [evalExprs?, ht, hd, EvalResult.bind, bind, pure]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc, him] using hb

end Benchmarks.Safe
