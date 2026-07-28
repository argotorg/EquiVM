import Examples.ERC20.Spec
import Solm.Notation

/-!
# ERC20 — the same spec, written in the Solidity-faithful Solm frontend

This regenerates the entire `ERC20.erc20Contract` (storage, constructor, all six transitions)
using `solidity%` from `Solm.Notation`, then proves the result is **definitionally equal** to the
hand-written AST in `Examples/ERC20/Spec.lean`.

Notes:
* The non-payable `require(msg.value == 0)` guards are implicit, as in Solidity.
* `from`/`to` are Lean keywords, so those parameter names are guillemet-escaped («from», «to»);
  `.getId.toString` still yields `"from"`/`"to"`, so the generated AST strings match.
* Transition order matches `erc20Contract.transitions` exactly (needed for `rfl`).
-/

open Solm Solm.Notation

namespace ERC20.Syntax

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

/-- The macro-generated contract is *definitionally* the hand-written one. -/
theorem contractSyntax_eq : contractSyntax = ERC20.erc20Contract := by rfl

end ERC20.Syntax
