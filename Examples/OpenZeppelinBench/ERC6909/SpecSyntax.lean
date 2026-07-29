import Examples.OpenZeppelinBench.ERC6909.Spec
import Solm.Notation

/-!
# ERC6909 spec in the Solidity-faithful Solm frontend

The OpenZeppelin `ERC6909Bench` spec written with `solidity%` and proven definitionally equal to
the AST spec in `Examples/OpenZeppelinBench/ERC6909/Spec.lean`.

The AST constructor has an empty body (no callvalue guard), so the surface constructor is an
empty `payable` one.  Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace OpenZeppelinBench.ERC6909.Syntax

def contractSyntax : ContractDecl := solidity% contract ERC6909Bench {
  mapping(address => mapping(uint256 => uint256)) _balances;
  mapping(address => mapping(address => bool)) _operatorApprovals;
  mapping(address => mapping(address => mapping(uint256 => uint256))) _allowances;

  constructor() payable { }

  function allowance(address owner, address spender, uint256 id) external returns (uint256) {
    return _allowances[owner][spender][id];
  }

  function approve(address spender, uint256 id, uint256 amount) external returns (bool) {
    require(msg.sender != address(0));
    require(spender != address(0));
    _allowances[msg.sender][spender][id] = amount;
    return true;
  }

  function balanceOf(address owner, uint256 id) external returns (uint256) {
    return _balances[owner][id];
  }

  function isOperator(address owner, address spender) external returns (bool) {
    return _operatorApprovals[owner][spender];
  }

  function setOperator(address spender, bool approved) external returns (bool) {
    require(msg.sender != address(0));
    require(spender != address(0));
    _operatorApprovals[msg.sender][spender] = approved;
    return true;
  }

  function supportsInterface(bytes4 interfaceId) external returns (bool) {
    return interfaceId == bytes4(0x0f632fb3) || interfaceId == bytes4(0x01ffc9a7);
  }

  function transfer(address receiver, uint256 id, uint256 amount) external returns (bool) {
    require(msg.sender != address(0));
    require(receiver != address(0));
    uint256 fromBalance = _balances[msg.sender][id];
    require(fromBalance >= amount);
    _balances[msg.sender][id] = fromBalance - amount;
    uint256 toBalance = _balances[receiver][id];
    _balances[receiver][id] = (toBalance + amount) as uint256;
    return true;
  }

  function transferFrom(address sender, address receiver, uint256 id, uint256 amount) external returns (bool) {
    if (sender != msg.sender && !_operatorApprovals[sender][msg.sender]) {
      uint256 currentAllowance = _allowances[sender][msg.sender][id];
      if (currentAllowance < type(uint256).max) {
        require(currentAllowance >= amount);
        _allowances[sender][msg.sender][id] = currentAllowance - amount;
      }
    }
    require(sender != address(0));
    require(receiver != address(0));
    uint256 fromBalance = _balances[sender][id];
    require(fromBalance >= amount);
    _balances[sender][id] = fromBalance - amount;
    uint256 toBalance = _balances[receiver][id];
    _balances[receiver][id] = (toBalance + amount) as uint256;
    return true;
  }
}

theorem contractSyntax_eq : contractSyntax = OpenZeppelinBench.ERC6909.contract := by rfl

end OpenZeppelinBench.ERC6909.Syntax
