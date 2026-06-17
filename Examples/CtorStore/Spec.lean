import Solm.Semantics
import Solm.SolidityLayout

/-!
# CtorStore — Solm specification for a constructor-storage equivalence test

The constructor takes a `uint256` argument and writes it to storage slot 0.  The storage field is
private so the runtime surface stays empty while the constructor proof exercises ABI arguments and
`SSTORE`.
-/

open Solm ABI Ethereum

namespace CtorStore

/-- The ABI/Solm type `uint256`. -/
def uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

/-- Storage layout: `stored` occupies the whole of slot 0. -/
def storageLayout : StorageLayout where
  layout := fun ref =>
    if ref.base = "stored" ∧ ref.steps = [] then
      some { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
             type := .int (.uint ⟨256, by decide⟩) }
    else none

/-- A payable constructor stores its `uint256` argument into slot 0. -/
def ctor : ConstructorDecl :=
  { params := [{ name := "x", ty := uint256 }]
    body := [ .assign { base := "stored" } (.var "x") ] }

/-- Solm specification of `CtorStore`; the private storage field has no public runtime transition. -/
def contract : ContractDecl :=
  { name := "CtorStore"
    storage := [{ name := "stored", ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    ctor := ctor
    transitions := [] }

end CtorStore

/-- Verification config: `stored` at slot 0 and Solidity constructor deployment encoding. -/
def ctorStoreConfig : Config :=
  { storage := CtorStore.storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment CtorStore.contract.ctor.params }
