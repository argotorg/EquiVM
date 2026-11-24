import Benchmarks.Safe.ViaIR.SetupSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_017

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSetupFallbackTrace (p : SetupInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata locals} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (if p.fallbackHandler = ⟨0⟩ then ⟨3401⟩ else ⟨3671⟩)
      (p.fallbackHandler :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hl : SetupLocals p locals) (hc : p.fallbackHandler.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt .reverted) ∨
    ∃ locals' evm' k' C',
      ExecStmt fork config { contract := contract, locals := locals } evm setupFallbackStmt
        (.ok { contract := contract, locals := locals' } evm') ∧
      SetupLocals p locals' ∧ evm'.executionEnv = I ∧ evm'.σ₀ = evm.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨3401⟩ (⟨0⟩ :: R) mem aw rdata evm'.accountMap k' C' := by
  by_cases hz : p.fallbackHandler = ⟨0⟩
  · simp only [hz, ite_true] at h
    rw [← hacc] at h
    exact .inr ⟨locals, evm, k, C, safeSetupFallbackSkip p evm hl hc hz, hl, hee, rfl, h⟩
  simp only [if_neg hz] at h
  have h₂ := safeRuntime_block_3671 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_3671_stack] at h₂
  by_cases heq : AccountAddress.ofNat p.fallbackHandler.toNat = I.codeOwner
  · have h₃ := safeRuntime_block_10675_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc,
        (canonicalAddress_eq_address_iff _ _ hc).mp heq, uInt256_eq_self]; decide)
      (by jump_dest) h₂
    exact .inl ⟨safeInternalFallbackTraceRevert h₃ (by simp; omega),
      safeSetupFallbackCall p evm hl hc hz
        (safeInternalSetFallbackHandlerRevert evm p.fallbackHandler (by rwa [hee]))⟩
  have h₃ := safeRuntime_block_10675_fallthrough (by simp; omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]
        exact uInt256_eq_zero_of_ne (fun hw ↦ heq
          ((canonicalAddress_eq_address_iff _ _ hc).mpr (uInt256_eq_one_eq hw).symm))) h₂
  obtain ⟨k', C', h₄⟩ := safeInternalFallbackTrace h₃ (by simp; omega) hperm (by jump_dest)
  have h₅ := safeRuntime_block_3680 (by simp; omega) (by jump_dest) h₄
  refine .inr ⟨locals.insert "_fallbackSet" .unit,
    Stele.EVM.storageStore evm evm.executionEnv.codeOwner fallbackHandlerSlot p.fallbackHandler,
    k' + 4, C' + 14, safeSetupFallbackCall p evm hl hc hz
      (safeInternalSetFallbackHandlerSource (fork := fork) (hperm := by simpa only [hee] using hperm) evm p.fallbackHandler hc (by rwa [hee])),
    hl.set _ _ (by decide), ?_, ?_, ?_⟩
  · simpa only [storageStore_executionEnv] using hee
  · exact storageStore_σ₀ _ _ _ _
  · simpa only [storageStore_accountMap, hee, hacc, safeRuntime_block_3680_stack] using h₅

end Benchmarks.Safe.ViaIR
