import Benchmarks.Safe.SetupAfterOwners
import Benchmarks.Safe.SetupEventTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupBodyTrace (evm : EVM.State)
    {I g s0 σ k C aw rdata n len} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4561⟩ (setupDecodedStack I.calldata n len (ret :: R))
      solcFreePtrMem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : SetupCalldataBounds I.calldata n len)
    (hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
      w.toNat < EVM.addressModulus)
    (hv : I.weiValue = ⟨0⟩) (hov : R.length + 36 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    VoidRoutineOutcome config (setupCalldataInput I.calldata n len).frame evm
      setupTransition.body safeBytecode I g s0 ret R := by
  let p := setupCalldataInput I.calldata n len
  have hv' : evm.executionEnv.weiValue = ⟨0⟩ := by rwa [hee]
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeSetupEventTrace h hb hc (by simp; omega)
  cases hperm : I.perm with
  | false =>
      exact .staticHalt (safeSetupStatic p evm hv' (by rwa [hee]))
        (safeSetupEventStatic h₁ hperm (by simp [setupEventSaved, setupDecodedStack]; omega))
  | true =>
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeSetupOwnersAllocate h₁ hb hperm (by simp; omega)
      obtain ⟨hrev, hs⟩ | ⟨f', evm', mem', aw₃, k₃, C₃, hs, hee', hw', h₃, hm', hr'⟩ :=
        safeSetupOwnersTrace p.ownersInput evm h₂ hee hacc
          (setupOwnersAllocatedMemory_words hb.ownersEnd) (by decide)
          (by change 128 + 32 + 32 * (calldataWords _ _ n).length < UInt256.size
              rw [calldataWords_length]; have := hb.ownersLength; norm_num [UInt256.size]; omega)
          (fun j hj ↦ hc _ (List.getElem_mem hj)) hperm
          (by simp [setupDecodedStack]; omega) (by jump_dest)
      · exact .reverted (safeSetupPrefix p evm hv'
          (.consRevert (safeSetupOwnersCall p evm (SetupLocals.initial p) hs))) hrev
      have hm : mem'.size = 288 + 32 * n :=
        hm'.trans (setupOwnersAllocatedMemory_size hb.ownersEnd)
      have hfree : memLoad ⟨64⟩ mem' = UInt256.ofNat (160 + 32 * n) := by
        have he : memLoad ⟨64⟩ mem' =
            memLoad ⟨64⟩ (setupOwnersAllocatedMemory I.calldata n) := by
          rw [memLoadReadWord, memLoadReadWord]
          exact congrArg uInt256OfByteArray (hr' 64 32 (by decide)
            (by rw [setupOwnersAllocatedMemory_size hb.ownersEnd]; omega))
        exact he.trans (setupOwnersAllocatedMemory_free hb.ownersEnd)
      have hzero : memLoad ⟨96⟩ mem' = ⟨0⟩ := by
        have he : memLoad ⟨96⟩ mem' =
            memLoad ⟨96⟩ (setupOwnersAllocatedMemory I.calldata n) := by
          rw [memLoadReadWord, memLoadReadWord]
          exact congrArg uInt256OfByteArray (hr' 96 32 (by decide)
            (by rw [setupOwnersAllocatedMemory_size hb.ownersEnd]; omega))
        exact he.trans (setupOwnersAllocatedMemory_zero hb.ownersEnd)
      have htail := safeSetupAfterOwners evm' h₃ hee' rfl (hw'.trans hworld)
        ((SetupLocals.initial p).set "_ownersSetup" .unit (by decide)) hb
        hfree (by omega) hzero hperm hov hret
      have hbody := htail.prepend (safeSetupOwnersCall p evm (SetupLocals.initial p) hs)
      cases hbody with
      | reverted source trace => exact .reverted (safeSetupPrefix p evm hv' source) trace
      | staticHalt source trace => exact .staticHalt (safeSetupPrefix p evm hv' source) trace
      | success source trace => exact .success (safeSetupPrefix p evm hv' source) trace

end Benchmarks.Safe
