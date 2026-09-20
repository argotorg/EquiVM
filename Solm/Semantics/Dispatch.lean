import ABI.Signature
import ABI.Decode
import Solm.Value
import Refinement.Result

/-! Message dispatch: selector, `receive`, and `fallback` resolution, argument binding, and return
conventions. -/


namespace Solm

open ABI

export Refinement (ReturnConvention ReturnConvention.abi ReturnConvention.rawBytes)


/-- Decode the calldata arguments and bind them to the parameter names. -/
def decodeCalldata (names : List Ident) (types : List ABIType) (calldata : ByteArray)
    (mode : DecodeMode := DecodeMode.modern) : Option Store := do
  let values <- decodeCalldataValues? types calldata mode
  insertValues names values ∅
  where
    insertValues : List Ident → List ABIValue → Store → Option Store
      | [], [], store => some store
      | name :: names, value :: values, store =>
          insertValues names values (store.insert name (Value.ofABI value))
      | _, _, _ => none

def decodeCalldataWithMode (mode : DecodeMode) (names : List Ident) (types : List ABIType)
    (calldata : ByteArray) : Option Store :=
  decodeCalldata names types calldata mode

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
