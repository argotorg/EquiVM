import ABI.Types
import ABI.Signature
import ABI.Decode
import ABI.Encode
import Act.Semantics

import Ethereum.Semantics
import Ethereum.Exception

namespace Act

open ABI

def transitionSignature (transition : TransitionDecl) : Signature :=
  ⟨transition.name, transition.params.map Param.ty⟩

def transitionSigStr (transition : TransitionDecl) : String :=
  printSignature $ transitionSignature transition

def dispatchMsg (contract : ContractDecl) (calldata : ByteArray)
  : Option TransitionDecl :=
  let sigs := contract.transitions.map (λ t ↦ (t, transitionSigStr t))
  let sigHashes := sigs.map (Prod.map id (ffi.KEC ∘ String.toByteArray))
  let selectors := sigHashes.map (Prod.map id (λ b ↦ b.extract 0 4))
  let currentSelector := calldata.extract 0 4
  match selectors.find? (λ (_,s) ↦ s == currentSelector) with
  | some (t,_) => t
  | none => .none -- fallback function/transition?

