import Solm.Semantics

namespace Solm

open ABI

theorem selectorDispatchMsg_eq_some_of_dispatchMsg_eq_some
    {contract : ContractDecl} {calldata : ByteArray} {transition : TransitionDecl}
    (hreceive : contract.receive = none)
    (hfallback : contract.fallback = none)
    (h : dispatchMsg contract calldata = some transition) :
    selectorDispatchMsg contract calldata = some transition := by
  unfold dispatchMsg at h
  cases hsel : selectorDispatchMsg contract calldata with
  | none =>
      have hreceiveDispatch : receiveDispatchMsg contract calldata = none := by
        simp [receiveDispatchMsg, hreceive]
      rw [hsel, hreceiveDispatch, hfallback] at h
      simp at h
  | some selected =>
      rw [hsel] at h
      simpa using h
