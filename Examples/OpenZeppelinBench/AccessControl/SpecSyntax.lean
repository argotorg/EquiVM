import Examples.OpenZeppelinBench.AccessControl.Spec
import Solm.Notation

/-!
# AccessControl spec in the Solidity-faithful Solm frontend

The OpenZeppelin `AccessControlBench` spec written with `solidity%` and proven definitionally
equal to the AST spec in `Examples/OpenZeppelinBench/AccessControl/Spec.lean`.

The AST constructor has no callvalue guard, so the surface constructor is marked `payable`.
`bytes32(0)` is the `DEFAULT_ADMIN_ROLE` fixed-bytes literal (defeq to `List.replicate 32 0`).
Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.AccessControl.Syntax

def contractSyntax : ContractDecl := solidity% contract AccessControlBench {
  struct RoleData {
    mapping(address => bool) hasRole;
    bytes32 adminRole;
  }

  mapping(bytes32 => RoleData) _roles;

  constructor() payable {
    _roles[bytes32(0)].hasRole[msg.sender] = true;
  }

  function DEFAULT_ADMIN_ROLE() external returns (bytes32) {
    return bytes32(0);
  }

  function getRoleAdmin(bytes32 role) external returns (bytes32) {
    return _roles[role].adminRole;
  }

  function grantRole(bytes32 role, address account) external {
    bytes32 adminRole = _roles[role].adminRole;
    require(_roles[adminRole].hasRole[msg.sender]);
    if (!_roles[role].hasRole[account]) {
      _roles[role].hasRole[account] = true;
    }
  }

  function hasRole(bytes32 role, address account) external returns (bool) {
    return _roles[role].hasRole[account];
  }

  function renounceRole(bytes32 role, address callerConfirmation) external {
    require(callerConfirmation == msg.sender);
    if (_roles[role].hasRole[callerConfirmation]) {
      _roles[role].hasRole[callerConfirmation] = false;
    }
  }

  function revokeRole(bytes32 role, address account) external {
    bytes32 adminRole = _roles[role].adminRole;
    require(_roles[adminRole].hasRole[msg.sender]);
    if (_roles[role].hasRole[account]) {
      _roles[role].hasRole[account] = false;
    }
  }

  function supportsInterface(bytes4 interfaceId) external returns (bool) {
    return interfaceId == bytes4(0x7965db0b) || interfaceId == bytes4(0x01ffc9a7);
  }
}

theorem contractSyntax_eq : contractSyntax = OpenZeppelinBench.AccessControl.contract := by rfl

end OpenZeppelinBench.AccessControl.Syntax
