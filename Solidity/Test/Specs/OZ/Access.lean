import Solidity.Test.Specs.OZ.Utils

/-!
# OpenZeppelin access-control bases (Solidity spec language)

Transcribed from `Examples/OpenZeppelinBench/vendor/openzeppelin-contracts/contracts/access/`:
`Ownable.sol`, `Ownable2Step.sol`, `IAccessControl.sol`, `AccessControl.sol`.
-/

namespace OpenZeppelinBench.OZ

open _root_.Solidity _root_.Solidity.Notation

def ownable : SourceUnit := sol% abstract contract Ownable is Context {
  address private _owner;

  error OwnableUnauthorizedAccount(address account);
  error OwnableInvalidOwner(address owner);

  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

  constructor(address initialOwner) {
    if (initialOwner == address(0)) {
      revert OwnableInvalidOwner(address(0));
    }
    _transferOwnership(initialOwner);
  }

  modifier onlyOwner() {
    _checkOwner();
    _;
  }

  function owner() public view virtual returns (address) {
    return _owner;
  }

  function _checkOwner() internal view virtual {
    if (owner() != _msgSender()) {
      revert OwnableUnauthorizedAccount(_msgSender());
    }
  }

  function renounceOwnership() public virtual onlyOwner {
    _transferOwnership(address(0));
  }

  function transferOwnership(address newOwner) public virtual onlyOwner {
    if (newOwner == address(0)) {
      revert OwnableInvalidOwner(address(0));
    }
    _transferOwnership(newOwner);
  }

  function _transferOwnership(address newOwner) internal virtual {
    address oldOwner = _owner;
    _owner = newOwner;
    emit OwnershipTransferred(oldOwner, newOwner);
  }
}

def ownable2Step : SourceUnit := sol% abstract contract Ownable2Step is Ownable {
  address private _pendingOwner;

  event OwnershipTransferStarted(address indexed previousOwner, address indexed newOwner);

  function pendingOwner() public view virtual returns (address) {
    return _pendingOwner;
  }

  function transferOwnership(address newOwner) public virtual override onlyOwner {
    _pendingOwner = newOwner;
    emit OwnershipTransferStarted(owner(), newOwner);
  }

  function _transferOwnership(address newOwner) internal virtual override {
    delete _pendingOwner;
    super._transferOwnership(newOwner);
  }

  function acceptOwnership() public virtual {
    address sender = _msgSender();
    if (pendingOwner() != sender) {
      revert OwnableUnauthorizedAccount(sender);
    }
    _transferOwnership(sender);
  }
}

def iAccessControl : SourceUnit := sol% interface IAccessControl {
  error AccessControlUnauthorizedAccount(address account, bytes32 neededRole);
  error AccessControlBadConfirmation();

  event RoleAdminChanged(bytes32 indexed role, bytes32 indexed previousAdminRole, bytes32 indexed newAdminRole);
  event RoleGranted(bytes32 indexed role, address indexed account, address indexed sender);
  event RoleRevoked(bytes32 indexed role, address indexed account, address indexed sender);

  function hasRole(bytes32 role, address account) external view returns (bool);
  function getRoleAdmin(bytes32 role) external view returns (bytes32);
  function grantRole(bytes32 role, address account) external;
  function revokeRole(bytes32 role, address account) external;
  function renounceRole(bytes32 role, address callerConfirmation) external;
}

def accessControl : SourceUnit := sol% abstract contract AccessControl is Context, IAccessControl, ERC165 {
  struct RoleData {
    mapping(address account => bool) hasRole;
    bytes32 adminRole;
  }

  mapping(bytes32 role => RoleData) private _roles;

  bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;

  modifier onlyRole(bytes32 role) {
    _checkRole(role);
    _;
  }

  function supportsInterface(bytes4 interfaceId) public view virtual override returns (bool) {
    return interfaceId == type(IAccessControl).interfaceId || super.supportsInterface(interfaceId);
  }

  function hasRole(bytes32 role, address account) public view virtual returns (bool) {
    return _roles[role].hasRole[account];
  }

  function _checkRole(bytes32 role) internal view virtual {
    _checkRole(role, _msgSender());
  }

  function _checkRole(bytes32 role, address account) internal view virtual {
    if (!hasRole(role, account)) {
      revert AccessControlUnauthorizedAccount(account, role);
    }
  }

  function getRoleAdmin(bytes32 role) public view virtual returns (bytes32) {
    return _roles[role].adminRole;
  }

  function grantRole(bytes32 role, address account) public virtual onlyRole(getRoleAdmin(role)) {
    _grantRole(role, account);
  }

  function revokeRole(bytes32 role, address account) public virtual onlyRole(getRoleAdmin(role)) {
    _revokeRole(role, account);
  }

  function renounceRole(bytes32 role, address callerConfirmation) public virtual {
    if (callerConfirmation != _msgSender()) {
      revert AccessControlBadConfirmation();
    }

    _revokeRole(role, callerConfirmation);
  }

  function _setRoleAdmin(bytes32 role, bytes32 adminRole) internal virtual {
    bytes32 previousAdminRole = getRoleAdmin(role);
    _roles[role].adminRole = adminRole;
    emit RoleAdminChanged(role, previousAdminRole, adminRole);
  }

  function _grantRole(bytes32 role, address account) internal virtual returns (bool) {
    if (!hasRole(role, account)) {
      _roles[role].hasRole[account] = true;
      emit RoleGranted(role, account, _msgSender());
      return true;
    } else {
      return false;
    }
  }

  function _revokeRole(bytes32 role, address account) internal virtual returns (bool) {
    if (hasRole(role, account)) {
      _roles[role].hasRole[account] = false;
      emit RoleRevoked(role, account, _msgSender());
      return true;
    } else {
      return false;
    }
  }
}

end OpenZeppelinBench.OZ
