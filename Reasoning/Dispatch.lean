import Solm.Dispatch
import Reasoning.Reach

/-!
# Dispatch — generic Solm `dispatchMsg` facts for a single-transition contract

For a contract with exactly one transition (`contract.transitions = [transition]`) whose 4-byte
keccak selector is `selBytes`, `dispatchMsg` reduces to a 4-byte calldata-prefix compare.  These
four lemmas are contract-agnostic; each example instantiates them with its `transitions = [t]`
proof (`rfl`) and its selector axiom.  `RDrev.reEquivNonPayable` (below) packages the whole
`callvalue ≠ 0` Solm-coupling on top of them.
-/

/- TODO generalize for an arbitrary number of transitions -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Reasoning.Theory

variable {contract : ContractDecl} {transition : TransitionDecl} {selBytes : ByteArray}

/-- `dispatchMsg` of a single-transition contract is the selector compare. -/
theorem dispatch_eq
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    (cd : ByteArray) :
    dispatchMsg contract cd = if (selBytes == cd.extract 0 4) then some transition else none := by
  simp only [dispatchMsg, htr, List.map_cons, List.map_nil, List.find?_cons, List.find?_nil,
    Prod.map, id_eq, Function.comp_apply]
  rw [hsel]
  by_cases hb : (selBytes == cd.extract 0 4) = true
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

/-- A single-transition contract dispatches only to that transition. -/
theorem dispatch_unique
    (htr : contract.transitions = [transition])
    {cd : ByteArray} {t : TransitionDecl} (h : dispatchMsg contract cd = some t) :
    t = transition := by
  simp only [dispatchMsg, htr, List.map_cons, List.map_nil] at h
  split at h
  · rename_i pair heq
    have hmem := List.mem_of_find?_eq_some heq
    simp only [List.mem_singleton, Prod.map, id_eq, Prod.mk.injEq] at hmem
    rw [Option.some.injEq] at h
    rw [← h, hmem.1]
  · exact absurd h (by simp)

/-- Calldata shorter than the 4-byte selector cannot dispatch. -/
theorem dispatch_none_short
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    (hsize : selBytes.size = 4) {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatch_eq htr hsel]
  have hfalse : (selBytes == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract] at hsz
    simp only [hsize] at hsz
    omega
  simp [hfalse]

/-- A selector mismatch cannot dispatch. -/
theorem dispatch_none_nomatch
    (htr : contract.transitions = [transition])
    (hsel : (ffi.KEC (String.toByteArray (Solm.transitionSigStr transition))).extract 0 4 = selBytes)
    {cd : ByteArray} (h : (selBytes == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  rw [dispatch_eq htr hsel]; simp [h]

/-- The EVM return bytes `o` couple to the Solm return value `rv` whenever `o` is `rv`'s ABI
    encoding (the `returned` case of `returnEquiv`). -/
theorem returnEquiv_of_encode {abit : ABIType} {rv : Value} {o : ByteArray}
    (h : encodeReturnValue? abit rv = some o) :
    returnEquiv o (some rv) (some abit) :=
  returnEquiv.returned rfl rfl h

end Reasoning.Theory

namespace Reasoning.Reach

/-- **The whole `callvalue ≠ 0` Solm coupling**, generic over a single-transition contract.  Given the
    non-payable guard's revert (`h : RDrev …`) and the contract body's revert under non-zero call
    value (`hbody`), produce the `runtimeEquivalenceFor` case: the OOG alternative folds via
    `reEquivElim`, and the Solm side is dispatched abstractly into `noDispatch` / `decodingFailed` /
    `execution`-with-revert.  Both examples' `callvalue ≠ 0` branch is a single call to this. -/
theorem RDrev.reEquivNonPayable {cfg : Config} {contract : ContractDecl} {transition : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (htr : contract.transitions = [transition])
    (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hbody : ∀ callargs, ExecContractBody cfg contract (initState cA gh bl σ σ₀ g A I)
              callargs transition.body .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => by
    by_cases hdisp : dispatchMsg contract I.calldata = none
    · exact reEquiv_noDispatch hdisp hrev
    · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
      cases Reasoning.Theory.dispatch_unique htr ht
      by_cases hdec : decodeCalldata (transition.params.map Param.name)
          (transitionSignature transition).paramTypes I.calldata = none
      · exact reEquiv_decodingFailed ht hdec hrev
      · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
        exact reEquiv_execution ht hca (hbody callargs) (by rw [hrev]; exact .revert rfl rfl)

/-- `RDret ⇒ execution` (success): the run returns bytes `o`, the dispatched Solm body returns
    `retVal` leaving the EVM state at `initState`, and `o` is `retVal`'s ABI encoding (`henc`). -/
theorem RDret.reEquivExecution {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray} {callargs cs retVal}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ) o)
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = some callargs)
    (hbody : ExecContractBody cfg contract (initState cA gh bl σ σ₀ g A I) callargs t.body
              (.returned cs (initState cA gh bl σ σ₀ g A I) retVal))
    (henc : returnEquiv o retVal t.returnType) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hsucc => by
    refine reEquiv_execution hd hdec hbody ?_
    rw [hsucc]; exact execResultsEquiv.success rfl rfl rfl rfl henc

/-- `RDrev ⇒ execution` (revert): the run reverts and the dispatched Solm body reverts too. -/
theorem RDrev.reEquivExecutionRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {cA gh bl σ σ₀ A I} {g : Sat256} {code : ByteArray} {callargs}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldata (t.params.map Param.name) (transitionSignature t).paramTypes
              I.calldata = some callargs)
    (hbody : ExecContractBody cfg contract (initState cA gh bl σ σ₀ g A I) callargs t.body .reverted) :
    runtimeEquivalenceFor cfg contract cA gh bl σ σ₀ g.toUInt256 A I :=
  h.reEquivElim hcode fun _ _ hrev => by
    refine reEquiv_execution hd hdec hbody ?_
    rw [hrev]; exact execResultsEquiv.revert rfl rfl

end Reasoning.Reach
