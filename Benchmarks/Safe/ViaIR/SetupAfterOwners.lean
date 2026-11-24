import Benchmarks.Safe.ViaIR.SetupFallbackTrace
import Benchmarks.Safe.ViaIR.SetupModulesCallTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

theorem safeSetupAfterOwners (evm : EVM.State)
    {I g s0 σ k C aw mem rdata n len locals} {R : List UInt256}
    (h : RD fork safeBytecode I g s0
      (if calldataWord I.calldata 132 = ⟨0⟩ then ⟨3401⟩ else ⟨3671⟩)
      (calldataWord I.calldata 132 :: UInt256.ofNat len ::
        UInt256.ofNat (setupDataStart I.calldata) :: ⟨3409⟩ ::
        calldataWord I.calldata 68 :: calldataWord I.calldata 68 ::
        calldataWord I.calldata 164 :: calldataWord I.calldata 228 ::
        calldataWord I.calldata 196 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals (setupCalldataInput I.calldata n len) locals)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat (160 + 32 * n))
    (hm : 128 ≤ mem.size) (hperm : I.perm = true) (hov : R.length + 36 ≤ 1024) :
    SetupTailOutcome fork (setupCalldataInput I.calldata n len)
      { contract := contract, locals := locals } evm (setupTransition.body.drop 4) g s0 := by
  let p := setupCalldataInput I.calldata n len
  obtain ⟨hrev, hs⟩ | ⟨locals', evm', k', C', hs, hl', hee', hw', h₁⟩ :=
    safeSetupFallbackTrace p evm h hee hacc hl hb.fallbackHandler hperm (by simp; omega)
  · exact .reverted (.consRevert hs) hrev
  have htail := safeSetupModulesCallTrace evm' h₁ hee' rfl (hw'.trans hworld) hl' hb
    hf hm hperm hov
  exact htail.prepend hs

end Benchmarks.Safe.ViaIR
