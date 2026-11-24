import Benchmarks.Safe.ViaIR.SetupAfterOwners
import Benchmarks.Safe.ViaIR.SetupEventTrace
import Benchmarks.Safe.ViaIR.SetupOwnersTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000

theorem safeSetupBodyTrace (evm : EVM.State)
    {I g s0 σ k C aw rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      solcFreePtrMem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hv : I.weiValue = ⟨0⟩) (hov : R.length + 36 ≤ 1024) :
    SetupOutcome fork (setupCalldataInput I.calldata n len).frame evm setupTransition.body g s0 := by
  let p := setupCalldataInput I.calldata n len
  have hv' : evm.executionEnv.weiValue = ⟨0⟩ := by rwa [hee]
  have hn : p.owners.length = n := calldataWords_length _ _ _
  have finish (hperm : I.perm = true) (htail : SetupTailOutcome fork p p.frame evm (setupTransition.body.drop 3) g s0) :
      SetupOutcome fork p.frame evm setupTransition.body g s0 := by
    cases htail with
    | allocationRevert bound trace =>
      exact .reverted (safeSetupAllocationRevert (fork := fork) (hperm := by simpa only [hee] using hperm) p evm hv' bound) trace
    | reverted source trace =>
      by_cases ha : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit
      · exact .reverted (safeSetupPrefix (fork := fork) (hperm := by simpa only [hee] using hperm) p evm hv' ha source) trace
      · exact .reverted (safeSetupAllocationRevert (fork := fork) (hperm := by simpa only [hee] using hperm) p evm hv' ha) trace
    | success bound source trace =>
      exact .success (safeSetupPrefix (fork := fork) (hperm := by simpa only [hee] using hperm) p evm hv' bound source) trace
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeSetupEventTrace h hb hc (by omega)
  cases hperm : I.perm with
  | false =>
    exact .staticHalt (safeSetupStatic p evm hv' (by rwa [hee]))
      (safeSetupEventStatic h₁ hperm (by omega))
  | true =>
    by_cases ha : 160 + 32 * n < 2 ^ 64
    swap
    · apply finish hperm
      refine .allocationRevert ?_ (safeSetupOwnersAllocateRevert h₁ hb ha hperm (by omega))
      intro hbound
      have hlim := le_trans hbound (safeSetupAllocationLimit_le p)
      rw [hn] at hlim
      omega
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeSetupOwnersAllocate h₁ hb hc ha hperm (by omega)
    simp only [setupOwnersSaved, List.cons_append, List.nil_append] at h₂
    obtain ⟨hrev, hs⟩ |
        ⟨f', evm', mem', aw₃, k₃, C₃, hs, hee', hw', h₃, hm', hr'⟩ :=
      safeSetupOwnersTrace p.ownersInput evm h₂ hee hacc
        (setupOwnersAllocatedMemory_words hb.ownersEnd) (by decide)
        (by change 128 + 32 + 32 * (calldataWords _ _ n).length < UInt256.size
            rw [calldataWords_length]
            change 128 + 32 + 32 * n < 2 ^ 256
            omega)
        (fun j hj ↦ hc _ (List.getElem_mem hj)) hperm (by omega)
    · exact finish hperm (.reverted (.consRevert
        (safeSetupOwnersCall p evm (SetupLocals.initial p) hs)) hrev)
    have hm : mem'.size = 288 + 32 * n :=
      hm'.trans (setupOwnersAllocatedMemory_size hb.ownersEnd)
    have hfree : memLoad ⟨64⟩ mem' = UInt256.ofNat (160 + 32 * n) := by
      have he : memLoad ⟨64⟩ mem' =
          memLoad ⟨64⟩ (setupOwnersAllocatedMemory I.calldata n) := by
        rw [memLoadReadWord, memLoadReadWord]
        exact congrArg uInt256OfByteArray (hr' 64 32 (by decide)
          (by rw [setupOwnersAllocatedMemory_size hb.ownersEnd]; omega))
      exact he.trans (setupOwnersAllocatedMemory_free hb.ownersEnd)
    have htail := safeSetupAfterOwners evm' h₃ hee' rfl (hw'.trans hworld)
      ((SetupLocals.initial p).set "_ownersSetup" .unit (by decide)) hb
      hfree (by omega) hperm hov
    exact finish hperm (htail.prepend (safeSetupOwnersCall p evm (SetupLocals.initial p) hs))

end Benchmarks.Safe.ViaIR
