import Solm.Semantics
import Solm.SolidityLayout
import Solm.MetaSolidityLayout

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

/-- A payable constructor stores its `uint256` argument into slot 0. -/
def ctor : ConstructorDecl :=
  { params := [{ name := "x", ty := uint256 }]
    body := [ .assign .storage { base := "stored" } (.var "x") ] }

/-- Solm specification of `CtorStore`; the private storage field has no public runtime transition. -/
def contract : ContractDecl :=
  { name := "CtorStore"
    storage := [{ name := "stored", ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    ctor := ctor
    transitions := [] }

/-- The generated Solidity backend for this contract's storage declarations. -/
def generatedStorageBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [contract.storage]

end CtorStore

/-- Verification config using generated storage operations and Solidity constructor encoding. -/
def ctorStoreConfig : Config :=
  { storageBackend := CtorStore.generatedStorageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment CtorStore.contract.ctor.params }

/-- The generated locator puts `stored` in slot 0. -/
theorem ctorStoreConfig_stored_location :
    ctorStoreConfig.storageBackend.locate? { base := "stored" } =
      some (.leaf { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
                    type := .int (.uint ⟨256, by decide⟩) }) := by
  rfl
