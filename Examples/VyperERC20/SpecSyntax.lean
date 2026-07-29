import Examples.VyperERC20.Spec
import Solm.Notation

/-!
# Vyper ERC20 spec in the Solidity-faithful Solm frontend

The Vyper ERC20 behavior spec is the language-agnostic ERC20 Solm AST
(`VyperERC20.erc20Contract` is `ERC20.erc20Contract`; only the storage layout is
Vyper-specific).  Written here with `solidity%` and proven definitionally equal.

`from`/`to` are Lean keywords, so those parameter names are guillemet-escaped.
Transition order matches `erc20Contract.transitions` exactly.
-/

open Solm Solm.Notation

namespace VyperERC20.Syntax

def contractSyntax : ContractDecl := solidity% contract ERC20 {
  mapping(address => uint256) balanceOf;
  mapping(address => mapping(address => uint256)) allowance;
  uint256 totalSupply;

  constructor(uint256 initialSupply) {
    balanceOf[msg.sender] = initialSupply;
    totalSupply = initialSupply;
  }

  function approve(address spender, uint256 value) external returns (bool) {
    allowance[msg.sender][spender] = value;
    return true;
  }

  function totalSupply() external returns (uint256) {
    return totalSupply;
  }

  function transferFrom(address «from», address «to», uint256 value) external returns (bool) {
    uint256 currentAllowance = allowance[«from»][msg.sender];
    require(currentAllowance >= value);
    uint256 fromBalance = balanceOf[«from»];
    require(fromBalance >= value);
    allowance[«from»][msg.sender] = currentAllowance - value;
    balanceOf[«from»] = (balanceOf[«from»] - value) as uint256;
    uint256 toBalance = balanceOf[«to»];
    uint256 newToBalance = (toBalance + value) as uint256;
    balanceOf[«to»] = newToBalance;
    return true;
  }

  function balanceOf(address owner) external returns (uint256) {
    return balanceOf[owner];
  }

  function transfer(address «to», uint256 value) external returns (bool) {
    uint256 fromBalance = balanceOf[msg.sender];
    require(fromBalance >= value);
    balanceOf[msg.sender] = fromBalance - value;
    uint256 toBalance = balanceOf[«to»];
    uint256 newToBalance = (toBalance + value) as uint256;
    balanceOf[«to»] = newToBalance;
    return true;
  }

  function allowance(address owner, address spender) external returns (uint256) {
    return allowance[owner][spender];
  }
}

theorem contractSyntax_eq : contractSyntax = VyperERC20.erc20Contract := by rfl

end VyperERC20.Syntax
