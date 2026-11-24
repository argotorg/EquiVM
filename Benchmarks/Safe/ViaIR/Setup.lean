import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.SetupDecoder
import Benchmarks.Safe.ViaIR.SetupBodyTrace
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005
import Benchmarks.Safe.ViaIR.Blocks.Runtime_014

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeSetupBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setupTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xb6 0x3e 0x80 0x0d ⟨0xb63e800d⟩
    hdispatch setupSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xb63e800d⟩ 17 ⟨2973⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_2973_taken (by simp) hvalue (by jump_dest) hentry
    have hr := safeRuntime_block_589 (by simp) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have hdecode := safeRuntime_block_2973_fallthrough (by simp) hvalue hentry
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata setupNames setupTypes I.calldata with
  | none =>
      have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
        obtain hr | ⟨n, len, k', C', hb, h₂⟩ :=
          safeDecodeSetupEvidence hdecode hlong hsize (by simp)
        · exact hr
        by_cases hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
            w.toNat < EVM.addressModulus
        · rw [decodeSetupBounded hb, if_pos hc] at hdec
          cases hdec
        exact safeSetupEventTraceRevert h₂ hb hc (by simp)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
      obtain ⟨n, len, hb, hc, rfl⟩ := decodeSetupEvidence hlong hdec
      have hdec' : config.externalABI.decodeCalldata?
          (setupTransition.params.map Param.name) (transitionSignature setupTransition).paramTypes
          I.calldata = some (setupCalldataInput I.calldata n len).args := hdec
      obtain ⟨k', C', h₂⟩ := safeDecodeSetupValid hdecode hb (by simp)
      have hbody := safeSetupBodyTrace evm h₂ rfl rfl rfl hb hc hvalue (by simp)
      cases hbody with
      | reverted source trace =>
          exact RDrev.reEquivElim hcode trace fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockRevert source) (.revert hΞ rfl)
      | staticHalt source trace =>
          exact RDstatic.reEquivElim hcode trace fun hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockStatic source) (.staticHalt hΞ rfl)
      | success source trace =>
          exact reEquivReturnElim hcode trace fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockOK source)
              (.success hΞ rfl rfl (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))

/-- Refinement obligation for `setup` (`setupTransition`). -/
theorem safeSetupRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setupTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeSetupBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
