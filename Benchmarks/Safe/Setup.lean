import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.SetupDecoder
import Benchmarks.Safe.SetupBodyTrace
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeSetupBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setupTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xb6 0x3e 0x80 0x0d ⟨0xb63e800d⟩
    hdispatch setupSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xb63e800d⟩ 2 ⟨1239⟩ hcode hsize hlong hword (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  swap
  · have h₁ := safeRuntime_block_1239_fallthrough (by simp) (isZero_eq_zero_of_ne hvalue) hentry
    have hr := safeRuntime_block_1247 (by simp [safeRuntime_block_1239_fallthrough_stack]) h₁
    exact reEquivSelectorRevert hcode hdispatch hr fun _ ↦ bodyReverts_nonPayable hvalue
  have h₁ := safeRuntime_block_1239_taken (by simp) (by rw [hvalue]; decide)
    (by jump_dest) hentry
  have hdecode := safeRuntime_block_1250 (by simp) (by jump_dest) h₁
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata setupNames setupTypes I.calldata with
  | none =>
      have hr : RDrev safeBytecode (.ofUInt256 g) evm := by
        obtain hr | ⟨n, len, k', C', hb, h₂⟩ :=
          safeDecodeSetupEvidence hdecode hlong hsize (by simp) (by jump_dest)
        · exact hr
        by_cases hc : ∀ w ∈ calldataWords I.calldata (setupOwnersStart I.calldata) n,
            w.toNat < EVM.addressModulus
        · rw [decodeSetupBounded hb, if_pos hc] at hdec
          cases hdec
        have h₃ := safeRuntime_block_1265 (by simp [setupDecodedStack]) (by jump_dest) h₂
        exact safeSetupEventTraceRevert h₃ hb hc (by simp)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
      obtain ⟨n, len, hb, hc, rfl⟩ := decodeSetupEvidence hlong hdec
      have hdec' : decodeCalldataWithMode config.abiDecodeMode
          (setupTransition.params.map Param.name) (transitionSignature setupTransition).paramTypes
          I.calldata = some (setupCalldataInput I.calldata n len).args := hdec
      obtain ⟨k', C', h₂⟩ := safeDecodeSetupValid hdecode hb (by simp) (by jump_dest)
      have h₃ := safeRuntime_block_1265 (by simp [setupDecodedStack]) (by jump_dest) h₂
      have hbody := safeSetupBodyTrace evm h₃ rfl rfl rfl hb hc hvalue (by simp) (by jump_dest)
      cases hbody with
      | reverted source trace =>
          exact RDrev.reEquivElim hcode trace fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockRevert source) (.revert hΞ rfl)
      | staticHalt source trace =>
          exact RDstatic.reEquivElim hcode trace fun hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockStatic source) (.staticHalt hΞ rfl)
      | success source trace =>
          have hr := safeRuntime_block_664 (by simp) trace
          exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
            reEquivSelectorExecution hdispatch hdec' (.execBlockOK source)
              (.success hΞ rfl rfl (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))

/-- Refinement obligation for `setup` (`setupTransition`). -/
theorem safeSetupRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some setupTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeSetupBodyCore hcode hsize hdispatch

end Benchmarks.Safe
