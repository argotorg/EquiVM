import Examples.OpenZeppelinBench.AccessControl.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace OpenZeppelinBench.AccessControl

/-!
# AccessControl benchmark trusted selector facts

The deployed runtime bytes and jump-destination table live in `Bytecode.lean`.  These selector
facts are isolated because `ffi.KEC` is opaque to Lean in this environment.
-/

/-- `keccak("supportsInterface(bytes4)")[0:4] = 0x01ffc9a7`. -/
axiom supportsInterfaceSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr supportsInterfaceTransition))).extract 0 4 =
      ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩

/-- `keccak("getRoleAdmin(bytes32)")[0:4] = 0x248a9ca3`. -/
axiom getRoleAdminSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr getRoleAdminTransition))).extract 0 4 =
      ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩

/-- `keccak("grantRole(bytes32,address)")[0:4] = 0x2f2ff15d`. -/
axiom grantRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr grantRoleTransition))).extract 0 4 =
      ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩

/-- `keccak("renounceRole(bytes32,address)")[0:4] = 0x36568abe`. -/
axiom renounceRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr renounceRoleTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩

/-- `keccak("hasRole(bytes32,address)")[0:4] = 0x91d14854`. -/
axiom hasRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr hasRoleTransition))).extract 0 4 =
      ⟨#[0x91, 0xd1, 0x48, 0x54]⟩

/-- `keccak("DEFAULT_ADMIN_ROLE()")[0:4] = 0xa217fddf`. -/
axiom defaultAdminRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr defaultAdminRoleTransition))).extract 0 4 =
      ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩

/-- `keccak("revokeRole(bytes32,address)")[0:4] = 0xd547741f`. -/
axiom revokeRoleSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr revokeRoleTransition))).extract 0 4 =
      ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩

end OpenZeppelinBench.AccessControl
