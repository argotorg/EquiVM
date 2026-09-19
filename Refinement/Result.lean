import EVM.Types
import ABI.Types

/-! # Result vocabulary shared by the refinement relations -/

namespace Refinement
open ABI

/-- How a call's result becomes bytes: ABI-encoded at the given types, or raw bytes. -/
inductive ReturnConvention where
  | abi : List ABIType → ReturnConvention
  | rawBytes : ReturnConvention
  deriving DecidableEq, Repr, Inhabited

/-- The EVM result type of `Ethereum.EVM.Ξ`. -/
abbrev EVMResult :=
  Except Ethereum.EVM.ExecutionException
    (Ethereum.ExecutionResult
      (Batteries.RBSet Ethereum.AccountAddress compare × Ethereum.AccountMap ×
        Ethereum.UInt256 × Ethereum.Substate))

/-- A storage well-formedness precondition: a predicate on the account map and the call environment. -/
abbrev StorageWF := Ethereum.AccountMap → Ethereum.ExecutionEnv → Prop

/-- Trivial storage well-formedness predicate for contracts whose correctness is unconditional. -/
def trivialStorageWF : StorageWF := fun _ _ => True

end Refinement
