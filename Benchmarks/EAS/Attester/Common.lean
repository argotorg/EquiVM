import Benchmarks.EAS.Attester.Selectors
import Benchmarks.EAS.Attester.ImmutableProofs
import Benchmarks.EAS.Attester.Blocks
import Reasoning.ABI
import Reasoning.Constructor
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody

/-!
# Attester proof prelude

Import point for the specification, patched bytecode, selectors, generated block summaries,
and shared refinement machinery. Functional proof obligations remain unproved.
`Audit.lean` is executable regression evidence and is deliberately separate from this prelude.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Reach

-- GENERALIZES Reasoning.Dispatch.RDrev.reEquivNonPayable to any number of transitions.
theorem RDrev.reEquivNonPayableOfMem {cfg : Config} {contract : ContractDecl}
    {immutables : Store} {σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code) (h : RDrev code g (initState σ σ₀ g A I))
    (hbody : ∀ t ∈ contract.transitions, ∀ callargs,
      ExecTransitionBody cfg contract (initState σ σ₀ g A I) callargs t.body
        .reverted immutables)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeRefinementFor cfg contract σ σ₀ g.toUInt256 A I immutables := by
  apply h.reEquivElim hcode
  intro _ _ hrev
  by_cases hdisp : dispatchMsg contract I.calldata = none
  · exact reEquiv_noDispatch hdisp hrev
  · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
    have htmem : t ∈ contract.transitions := by
      rw [dispatchMsg_eq_dispatchList contract I.calldata hfallback hreceive] at ht
      exact dispatchList_some_mem ht
    by_cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
        (transitionSignature t).paramTypes I.calldata = none
    · exact reEquiv_decodingFailed ht hdec hrev hfallback hreceive
    · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
      exact reEquiv_execution ht hca (hbody t htmem callargs)
        (by rw [hrev]; exact execResultsEquiv.revert rfl rfl) hfallback hreceive

end Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem contract_transitions :
    contract.transitions =
      [attestTransition, multiAttestTransition, multiRevokeTransition, revokeTransition] := rfl

theorem attesterAttestEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨0x72b9966d⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩) =
      if attesterAttestSelBytes == cd.extract 0 4 then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x72 0xb9 0x96 0x6d ⟨0x72b9966d⟩ (by decide)

theorem attesterRevokeEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨0xc2664610⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩) =
      if attesterRevokeSelBytes == cd.extract 0 4 then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0xc2 0x66 0x46 0x10 ⟨0xc2664610⟩ (by decide)

theorem attesterMultiAttestEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨0x54e1db35⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩) =
      if attesterMultiAttestSelBytes == cd.extract 0 4 then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x54 0xe1 0xdb 0x35 ⟨0x54e1db35⟩ (by decide)

theorem attesterMultiRevokeEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨0x13fde550⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩) =
      if attesterMultiRevokeSelBytes == cd.extract 0 4 then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x13 0xfd 0xe5 0x50 ⟨0x13fde550⟩ (by decide)

end Benchmarks.EAS.Attester
