import Benchmarks.Safe.SetupSource
import Benchmarks.Safe.Blocks.Runtime_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupFallbackTrace (p : SetupInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata locals} {x0 x1 x2 : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4695⟩
      (x0 :: x1 :: x2 :: p.fallbackHandler :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecStmt config { contract := contract, locals := locals } evm setupFallbackStmt .reverted) ∨
    ∃ locals' evm' k' C',
      ExecStmt config { contract := contract, locals := locals } evm setupFallbackStmt
        (.ok { contract := contract, locals := locals' } evm') ∧
      SetupLocals p locals' ∧ evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD safeBytecode I g s0 ⟨4719⟩
        (x0 :: x1 :: x2 :: p.fallbackHandler :: R) mem aw rdata evm'.accountMap k' C' := by
  by_cases hz : p.fallbackHandler = ⟨0⟩
  · have h₁ := safeRuntime_block_4695_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
    rw [← hacc] at h₁
    exact .inr ⟨locals, evm, _, _, safeSetupFallbackSkip p evm hl hc hz, hl, hee, rfl, h₁⟩
  have h₁ := safeRuntime_block_4695_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
  have h₂ := safeRuntime_block_4711 (by omega) (by jump_dest) h₁
  simp only [safeRuntime_block_4711_stack] at h₂
  by_cases heq : AccountAddress.ofNat p.fallbackHandler.toNat = I.codeOwner
  · have h₃ := safeRuntime_block_8250_fallthrough (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]
          exact u256_sub_eq_zero_iff_eq.mpr
            ((canonicalAddress_eq_address_iff _ _ hc).mp heq)) h₂
    exact .inl ⟨safeInternalFallbackTraceRevert h₃ (by simp; omega),
      safeSetupFallbackCall p evm hl hc hz
        (safeInternalSetFallbackHandlerRevert evm p.fallbackHandler (by rwa [hee]))⟩
  have h₃ := safeRuntime_block_8250_taken (by simp; omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]
        exact u256_sub_ne_zero_of_ne
          (fun hw ↦ heq ((canonicalAddress_eq_address_iff _ _ hc).mpr hw))) (by jump_dest) h₂
  obtain ⟨k', C', h₄⟩ := safeInternalFallbackTrace h₃ (by simp; omega) hperm (by jump_dest)
  refine .inr ⟨locals.insert "_fallbackSet" .unit,
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot p.fallbackHandler,
    k', C', safeSetupFallbackCall p evm hl hc hz
      (safeInternalSetFallbackHandlerSource evm p.fallbackHandler hc (by rwa [hee])),
    hl.set _ _ (by decide), ?_, ?_, ?_⟩
  · simpa only [storageStore_executionEnv] using hee
  · exact storageStore_σ₀ _ _ _ _
  · simpa only [storageStore_accountMap, hee, hacc] using h₄

end Benchmarks.Safe
