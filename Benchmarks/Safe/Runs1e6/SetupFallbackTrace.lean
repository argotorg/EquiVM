import Benchmarks.Safe.Runs1e6.SetupSource
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_023
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_036

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

theorem safeSetupFallbackTrace (p : SetupInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata locals} {x0 x1 x2 : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5482⟩
      (x0 :: x1 :: x2 :: p.fallbackHandler :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt .reverted) ∨
    ∃ locals' evm' k' C',
      ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt
        (.ok { contract := contract, locals := locals' } evm') ∧
      SetupLocals p locals' ∧ evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨5519⟩
        (x0 :: x1 :: x2 :: p.fallbackHandler :: R) mem aw rdata evm'.accountMap k' C' := by
  by_cases hz : p.fallbackHandler = ⟨0⟩
  · have h₁ := safeRuntime_block_5482_taken (by omega)
      (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
    rw [← hacc] at h₁
    exact .inr ⟨locals, evm, _, _, safeSetupFallbackSkip p evm hl hc hz, hl, hee, rfl, h₁⟩
  have h₁ := safeRuntime_block_5482_fallthrough (by omega)
    (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
  have h₂ := safeRuntime_block_5511 (by omega) (by jump_dest) h₁
  simp only [safeRuntime_block_5511_stack] at h₂
  by_cases heq : AccountAddress.ofNat p.fallbackHandler.toNat = I.codeOwner
  · have h₃ := safeRuntime_block_10293_fallthrough (by simp; omega)
      (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc]
          exact u256_sub_eq_zero_iff_eq.mpr
            ((canonicalAddress_eq_address_iff _ _ hc).mp heq)) h₂
    exact .inl ⟨safeInternalFallbackTraceRevert h₃ (by simp; omega),
      safeSetupFallbackCall p evm hl hc hz
        (safeInternalSetFallbackHandlerRevert evm p.fallbackHandler (by rwa [hee]))⟩
  have h₃ := safeRuntime_block_10293_taken (by simp; omega)
    (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc]
        exact u256_sub_ne_zero_of_ne
          (fun hw ↦ heq ((canonicalAddress_eq_address_iff _ _ hc).mpr hw))) (by jump_dest) h₂
  obtain ⟨k', C', h₄⟩ := safeInternalFallbackTrace h₃ (by simp; omega) hperm (by jump_dest)
  refine .inr ⟨locals.insert "_fallbackSet" .unit,
    Stele.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot p.fallbackHandler,
    k', C', safeSetupFallbackCall p evm hl hc hz
      (safeInternalSetFallbackHandlerSource (fork := fork) (hperm := by simpa only [hee] using hperm) evm p.fallbackHandler hc (by rwa [hee])),
    hl.set _ _ (by decide), ?_, ?_, ?_⟩
  · simpa only [storageStore_executionEnv] using hee
  · exact storageStore_σ₀ _ _ _ _
  · simpa only [storageStore_accountMap, hee, hacc] using h₄

end Benchmarks.Safe.Runs1e6
