import Benchmarks.Safe.SetupFallbackTrace
import Benchmarks.Safe.SetupModulesCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSetupAfterOwners (evm : EVM.State)
    {I g s0 σ k C aw mem rdata n len locals} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4695⟩ (setupDecodedStack I.calldata n len (ret :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals (setupCalldataInput I.calldata n len) locals)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat (160 + 32 * n))
    (hm : 128 ≤ mem.size) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hperm : I.perm = true) (hov : R.length + 36 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    VoidRoutineOutcome config { contract := contract, locals := locals } evm
      (setupTransition.body.drop 3) safeBytecode I g s0 ret R := by
  let p := setupCalldataInput I.calldata n len
  obtain ⟨hrev, hs⟩ | ⟨locals', evm', k', C', hs, hl', hee', hw', h₁⟩ :=
    safeSetupFallbackTrace p evm h hee hacc hl hb.fallbackHandler hperm
      (by simp; omega)
  · exact .reverted (.consRevert hs) hrev
  have htail := safeSetupModulesCallTrace evm' h₁ hee' rfl (hw'.trans hworld) hl' hb
    hf hm (by omega) hz (by have := hb.ownersLength; have := hb.dataLength; omega)
    hperm hov hret
  exact htail.prepend hs

end Benchmarks.Safe
