import ABI.Signature
import Solm.Value

/-! Message dispatch: selector, `receive`, and `fallback` resolution, and return conventions. -/

namespace Solm

open ABI

def transitionSignature (transition : TransitionDecl) : Signature :=
  ⟨transition.name, transition.params.map Param.ty⟩

def transitionSigStr (transition : TransitionDecl) : String :=
  printSignature $ transitionSignature transition

def selectorDispatchMsg (contract : ContractDecl) (calldata : ByteArray)
  : Option TransitionDecl :=
  let sigs := contract.transitions.map (λ t ↦ (t, transitionSigStr t))
  let sigHashes := sigs.map (Prod.map id (ffi.KEC ∘ String.toByteArray))
  let selectors := sigHashes.map (Prod.map id (λ b ↦ b.extract 0 4))
  let currentSelector := calldata.extract 0 4
  match selectors.find? (λ (_,s) ↦ s == currentSelector) with
  | some (t,_) => t
  | none => none

def receiveDispatchMsg (contract : ContractDecl) (calldata : ByteArray)
  : Option TransitionDecl :=
  if calldata.size = 0 then contract.receive else none

def dispatchMsg (contract : ContractDecl) (calldata : ByteArray)
  : Option TransitionDecl :=
  match selectorDispatchMsg contract calldata with
  | some transition => some transition
  | none =>
      match receiveDispatchMsg contract calldata with
      | some transition => some transition
      | none => contract.fallback

inductive ReturnConvention where
  | abi : List ABIType → ReturnConvention
  | rawBytes : ReturnConvention
  deriving DecidableEq, Repr, Inhabited

def fallbackCallargs (calldata : ByteArray) : List Param → Option Store
  | [] => some ∅
  | [param] =>
      match param.ty with
      | .bytes => some ((∅ : Store).insert param.name (.bytes calldata))
      | _ => none
  | _ => none

def fallbackReturnConvention (transition : TransitionDecl) : Option ReturnConvention :=
  match transition.params, transition.returnType with
  | [], [] => some (.abi [])
  | [param], [.bytes] =>
      match param.ty with
      | .bytes => some .rawBytes
      | _ => none
  | _, _ => none

end Solm
