import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.ExecTransactionDecoderEvidence
import Benchmarks.Safe.ViaIR.ExecTransactionBodyTrace
import Benchmarks.Safe.ViaIR.Routines

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

set_option maxRecDepth 100000 in
theorem safeExectransactionBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some exectransactionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x6a 0x76 0x12 0x02 ⟨0x6a761202⟩
    hdispatch exectransactionSelectorBytes (by decide)
  obtain ⟨k, C, hentry⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x6a761202⟩ 11 ⟨4354⟩ hcode hsize hlong hword (by native_decide)
  let evm := initState σ σ₀ (.ofUInt256 g) A I
  cases hdec : decodeCalldata execTransactionNames execTransactionTypes I.calldata with
  | none =>
    have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
      obtain hr | ⟨dataLen, sigLen, _, _, _, hb, _, _, _⟩ :=
        safeDecodeExecTransactionEvidence hentry hlong hsize (by simp)
      · exact hr
      rw [decodeExecTransactionValid hb] at hdec
      cases hdec
    exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch hdec hr
  | some args =>
    obtain ⟨dataLen, sigLen, hb, rfl⟩ := decodeExecTransactionEvidence hlong hdec
    let p := execTransactionCalldataInput I.calldata dataLen sigLen
    have hlen : p.signatures.size = sigLen := execTransactionSignaturesSize hb
    have hdec' : config.externalABI.decodeCalldata?
        (exectransactionTransition.params.map Param.name)
        (transitionSignature exectransactionTransition).paramTypes I.calldata = some p.args :=
      hdec
    by_cases hvalid : sigLen ≤ 2 ^ 64 - 192 ∧ (calldataWord I.calldata 100).toNat < 2
    · obtain ⟨aw', k', C', h₁⟩ := safeDecodeExecTransactionValid hentry hb hvalid.2 hvalid.1
        (by simp)
      obtain ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨frame', evm', σ', z, hs, he', ha', hw', hr⟩ :=
        safeExecTransactionBodyTrace evm h₁ rfl rfl rfl hb hvalid.2 hvalid.1 (by simp)
      · exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hs (.revert hΞ rfl)
      · exact RDstatic.reEquivElim hcode hr fun hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hs (.staticHalt hΞ rfl)
      · exact reEquivReturnElim hcode hr fun _ _ hΞ ↦
          reEquivSelectorExecution hdispatch hdec' hs
            (.success hΞ rfl ha'.symm (.abi (returnEquiv_of_encode (boolReturnEncoding z))))
    · have hr : RDrev fork safeBytecode (.ofUInt256 g) evm := by
        obtain hr | ⟨dataLen', sigLen', _, _, _, hb', ho', hn', _⟩ :=
          safeDecodeExecTransactionEvidence hentry hlong hsize (by simp)
        · exact hr
        have heq : sigLen = sigLen' := by
          have ht := congrArg UInt256.toNat (hb.sigWord.symm.trans hb'.sigWord)
          have hsn := hb.sigLength
          have hsn' := hb'.sigLength
          rw [ulit_toNat' _ (by change sigLen < 2 ^ 256; omega),
            ulit_toNat' _ (by change sigLen' < 2 ^ 256; omega)] at ht
          exact ht
        exact (hvalid ⟨heq.symm ▸ hn', ho'⟩).elim
      have hs : ExecTransitionBody fork config contract evm p.args
          exectransactionTransition.body .reverted := by
        refine .execBlockRevert ?_
        by_cases hn : sigLen ≤ 2 ^ 64 - 192
        · exact safeExecTransactionInvalidOperation p evm (fun ho ↦ hvalid ⟨hn, ho⟩)
        · exact safeExecTransactionLargeSignatures p evm (by rwa [hlen])
      exact RDrev.reEquivElim hcode hr fun _ _ hΞ ↦
        reEquivSelectorExecution hdispatch hdec' hs (.revert hΞ rfl)

/-- Refinement obligation for `execTransaction` (`exectransactionTransition`). -/
theorem safeExectransactionRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some exectransactionTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeExectransactionBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
