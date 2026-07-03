import Solm.Semantics
import Solm.SolidityLayout

/-!
# CtorTruth — Solm specification for a constructor-equivalence smoke test

The payable empty constructor keeps the initcode trace small, while still exercising the
constructor-equivalence API and Solidity deployment hook.
-/

open Solm ABI

namespace CtorTruth

/-- The runtime transition is the same shape as `Truth.truth()`. -/
def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
      , .return [(.boolLit true)] ] }

/-- A payable constructor avoids Solidity's non-payable constructor guard. -/
def ctor : ConstructorDecl :=
  { params := []
    body := [] }

/-- Solm specification of `CtorTruth`. -/
def contract : ContractDecl :=
  { name := "CtorTruth"
    storage := []
    ctor := ctor
    transitions := [truthTransition] }

end CtorTruth

/-- Configuration: empty storage layout and Solidity constructor deployment encoding. -/
def ctorTruthConfig : Config :=
  { storage := { layout := fun _ _ => none }
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment CtorTruth.contract.ctor.params }
