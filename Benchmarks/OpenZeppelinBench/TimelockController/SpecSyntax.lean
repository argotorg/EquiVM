import Benchmarks.OpenZeppelinBench.TimelockController.Spec
import Solm.Notation

/-!
# TimelockController spec in the Solidity-faithful Solm frontend

The whole TimelockControllerBench benchmark spec, written with `solidity%` and proven
definitionally equal to the AST spec in `Benchmarks/OpenZeppelinBench/TimelockController/Spec.lean`.

Notes mirroring the AST spec:
* Role constants are the keccak hashes from the optimized runtime, written as `bytes32(0x…)`
  literals; `DEFAULT_ADMIN_ROLE` is `bytes32(0x0)`.
* Operation-id hashing goes through the benchmark-local ABI hooks
  (`abi.encodeWithSelector(__abi_encode_hashOperation…, …)` → `Expr.abiEncodeCall`).
* The constructor and `execute`/`executeBatch` bodies carry no callvalue guard in the AST spec,
  so they are marked `payable` here.
* `executeBatch`'s loop body calls `targets[i].call{value: values[i]}(payloads[i])`; an indexed
  low-level-call receiver has no surface form, so the body splices the spec's own `rawExecute`.
* Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.TimelockController.Syntax

def contractSyntax : ContractDecl := solidity% contract TimelockControllerBench {
  struct RoleData {
    mapping(address => bool) hasRole;
    bytes32 adminRole;
  }

  mapping(bytes32 => RoleData) _roles;
  mapping(bytes32 => uint256) _timestamps;
  uint256 _minDelay;

  constructor() payable {
    if (!_roles[bytes32(0x0)].hasRole[address(this)]) {
      _roles[bytes32(0x0)].hasRole[address(this)] = true;
    }
    if (msg.sender != address(0)) {
      if (!_roles[bytes32(0x0)].hasRole[msg.sender]) {
        _roles[bytes32(0x0)].hasRole[msg.sender] = true;
      }
    }
    if (!_roles[bytes32(0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1)].hasRole[msg.sender]) {
      _roles[bytes32(0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1)].hasRole[msg.sender] = true;
    }
    if (!_roles[bytes32(0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783)].hasRole[msg.sender]) {
      _roles[bytes32(0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783)].hasRole[msg.sender] = true;
    }
    if (!_roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[address(0)]) {
      _roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[address(0)] = true;
    }
    _minDelay = 86400;
  }

  function CANCELLER_ROLE() external view returns (bytes32) {
    return bytes32(0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783);
  }

  function cancel(bytes32 id) external {
    require(_roles[bytes32(0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783)].hasRole[msg.sender]);
    require(_timestamps[id] > 1);
    delete _timestamps[id];
  }

  function DEFAULT_ADMIN_ROLE() external view returns (bytes32) {
    return bytes32(0x0);
  }

  function executeBatch(address[] calldata targets, uint256[] calldata values,
      bytes[] calldata payloads, bytes32 predecessor, bytes32 salt) external payable {
    if (!_roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[address(0)]) {
      require(_roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[msg.sender]);
    }
    require(targets.length == values.length);
    require(targets.length == payloads.length);
    bytes32 id = keccak256(abi.encodeWithSelector(__abi_encode_hashOperationBatch,
      targets, values, payloads, predecessor, salt));
    require(_timestamps[id] > 1 && _timestamps[id] <= block.timestamp);
    if (predecessor != bytes32(0x0)) {
      require(_timestamps[predecessor] == 1);
    }
    for (uint256 i = 0; i < targets.length; i = (i + 1) as uint256) {
      ${rawExecute (.index (.var "targets") (.var "i")) (.index (.var "values") (.var "i"))
          (.index (.var "payloads") (.var "i"))}
    }
    require(_timestamps[id] > 1 && _timestamps[id] <= block.timestamp);
    _timestamps[id] = 1;
  }

  function execute(address target, uint256 value, bytes calldata payload,
      bytes32 predecessor, bytes32 salt) external payable {
    if (!_roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[address(0)]) {
      require(_roles[bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63)].hasRole[msg.sender]);
    }
    bytes32 id = keccak256(abi.encodeWithSelector(__abi_encode_hashOperation,
      target, value, payload, predecessor, salt));
    require(_timestamps[id] > 1 && _timestamps[id] <= block.timestamp);
    if (predecessor != bytes32(0x0)) {
      require(_timestamps[predecessor] == 1);
    }
    (bool success, bytes memory returndata) = target.call{value: value}(payload);
    require(success);
    require(_timestamps[id] > 1 && _timestamps[id] <= block.timestamp);
    _timestamps[id] = 1;
  }

  function EXECUTOR_ROLE() external view returns (bytes32) {
    return bytes32(0xd8aa0f3194971a2a116679f7c2090f6939c8d4e01a2a8d7e41d55e5351469e63);
  }

  function getMinDelay() external view returns (uint256) {
    return _minDelay;
  }

  function getOperationState(bytes32 id) external view returns (uint8) {
    return _timestamps[id] == 0 ? 0
      : (_timestamps[id] == 1 ? 3 : (_timestamps[id] > block.timestamp ? 1 : 2));
  }

  function getRoleAdmin(bytes32 role) external view returns (bytes32) {
    return _roles[role].adminRole;
  }

  function getTimestamp(bytes32 id) external view returns (uint256) {
    return _timestamps[id];
  }

  function grantRole(bytes32 role, address account) external {
    bytes32 adminRole = _roles[role].adminRole;
    require(_roles[adminRole].hasRole[msg.sender]);
    if (!_roles[role].hasRole[account]) {
      _roles[role].hasRole[account] = true;
    }
  }

  function hasRole(bytes32 role, address account) external view returns (bool) {
    return _roles[role].hasRole[account];
  }

  function hashOperationBatch(address[] calldata targets, uint256[] calldata values,
      bytes[] calldata payloads, bytes32 predecessor, bytes32 salt) external view returns (bytes32) {
    return keccak256(abi.encodeWithSelector(__abi_encode_hashOperationBatch,
      targets, values, payloads, predecessor, salt));
  }

  function hashOperation(address target, uint256 value, bytes calldata data,
      bytes32 predecessor, bytes32 salt) external view returns (bytes32) {
    return keccak256(abi.encodeWithSelector(__abi_encode_hashOperation,
      target, value, data, predecessor, salt));
  }

  function isOperationDone(bytes32 id) external view returns (bool) {
    return _timestamps[id] == 1;
  }

  function isOperationPending(bytes32 id) external view returns (bool) {
    return _timestamps[id] > 1;
  }

  function isOperationReady(bytes32 id) external view returns (bool) {
    return _timestamps[id] > 1 && _timestamps[id] <= block.timestamp;
  }

  function isOperation(bytes32 id) external view returns (bool) {
    return _timestamps[id] != 0;
  }

  function onERC1155BatchReceived(address operator, address «from», uint256[] calldata ids,
      uint256[] calldata values, bytes calldata data) external returns (bytes4) {
    return bytes4(0xbc197c81);
  }

  function onERC1155Received(address operator, address «from», uint256 id,
      uint256 value, bytes calldata data) external returns (bytes4) {
    return bytes4(0xf23a6e61);
  }

  function onERC721Received(address operator, address «from», uint256 tokenId,
      bytes calldata data) external returns (bytes4) {
    return bytes4(0x150b7a02);
  }

  function PROPOSER_ROLE() external view returns (bytes32) {
    return bytes32(0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1);
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

  function scheduleBatch(address[] calldata targets, uint256[] calldata values,
      bytes[] calldata payloads, bytes32 predecessor, bytes32 salt, uint256 delay) external {
    require(_roles[bytes32(0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1)].hasRole[msg.sender]);
    require(targets.length == values.length);
    require(targets.length == payloads.length);
    bytes32 id = keccak256(abi.encodeWithSelector(__abi_encode_hashOperationBatch,
      targets, values, payloads, predecessor, salt));
    require(!(_timestamps[id] != 0));
    uint256 minDelay = _minDelay;
    require(delay >= minDelay);
    _timestamps[id] = (block.timestamp + delay) as uint256;
  }

  function schedule(address target, uint256 value, bytes calldata data,
      bytes32 predecessor, bytes32 salt, uint256 delay) external {
    require(_roles[bytes32(0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1)].hasRole[msg.sender]);
    bytes32 id = keccak256(abi.encodeWithSelector(__abi_encode_hashOperation,
      target, value, data, predecessor, salt));
    require(!(_timestamps[id] != 0));
    uint256 minDelay = _minDelay;
    require(delay >= minDelay);
    _timestamps[id] = (block.timestamp + delay) as uint256;
  }

  function supportsInterface(bytes4 interfaceId) external view returns (bool) {
    return interfaceId == bytes4(0x4e2312e0)
      || interfaceId == bytes4(0x7965db0b)
      || interfaceId == bytes4(0x01ffc9a7);
  }

  function updateDelay(uint256 newDelay) external {
    require(msg.sender == address(this));
    _minDelay = newDelay;
  }

  receive() external payable { }
}

theorem contractSyntax_eq :
    contractSyntax = OpenZeppelinBench.TimelockController.contract := by rfl

end OpenZeppelinBench.TimelockController.Syntax
