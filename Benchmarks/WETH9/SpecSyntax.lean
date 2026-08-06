import Benchmarks.WETH9.Spec
import Solm.Notation

/-!
# WETH9 spec in the Solidity-faithful Solm frontend

The whole WETH9 benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/WETH9/Spec.lean`.

Notes mirroring the AST spec:
* WETH9.sol has no explicit constructor; solc emits a non-payable implicit one that only runs the
  field initializers — written here as a non-payable `constructor()` with the assignments.
* The payable Solidity fallback is the deposit body.
* `transfer` forwards through the public `transferFrom` (an internal dispatch, hence the
  explicitly bound `var _ok = transferFrom(…)`).
* Transition order matches `contract.transitions` exactly.
-/

open Solm Solm.Notation

namespace Benchmarks.WETH9.Syntax

def contractSyntax : ContractDecl := solidity% contract WETH9 {
  string name;
  string symbol;
  uint8 decimals;
  mapping(address => uint256) balanceOf;
  mapping(address => mapping(address => uint256)) allowance;

  constructor() {
    name = "Wrapped Ether";
    symbol = "WETH";
    decimals = 18;
  }

  function name() external returns (string) {
    return name;
  }

  function approve(address guy, uint256 wad) external returns (bool) {
    allowance[msg.sender][guy] = wad;
    return true;
  }

  function totalSupply() external returns (uint256) {
    return address(this).balance;
  }

  function transferFrom(address src, address dst, uint256 wad) external returns (bool) {
    require(balanceOf[src] >= wad);
    if (src != msg.sender && allowance[src][msg.sender] != type(uint256).max) {
      require(allowance[src][msg.sender] >= wad);
      allowance[src][msg.sender] = ${Expr.binary (.sub uint256Int .wrapping)
        (.storage (allowanceRef (.var "src") sender)) (.var "wad")};
    }
    balanceOf[src] = ${Expr.binary (.sub uint256Int .wrapping)
      (.storage (balanceOfRef (.var "src"))) (.var "wad")};
    balanceOf[dst] = ${Expr.binary (.add uint256Int .wrapping)
      (.storage (balanceOfRef (.var "dst"))) (.var "wad")};
    return true;
  }

  function withdraw(uint256 wad) external {
    require(balanceOf[msg.sender] >= wad);
    balanceOf[msg.sender] = ${Expr.binary (.sub uint256Int .wrapping)
      (.storage (balanceOfRef sender)) (.var "wad")};
    (bool success, bytes memory _data) = msg.sender.call{value: wad}(new bytes(0));
    require(success);
  }

  function decimals() external returns (uint8) {
    return decimals;
  }

  function balanceOf(address owner) external returns (uint256) {
    return balanceOf[owner];
  }

  function symbol() external returns (string) {
    return symbol;
  }

  function transfer(address dst, uint256 wad) external returns (bool) {
    var _ok = transferFrom(msg.sender, dst, wad);
    return _ok;
  }

  function deposit() external payable {
    balanceOf[msg.sender] = ${Expr.binary (.add uint256Int .wrapping)
      (.storage (balanceOfRef sender)) (.env .callvalue)};
  }

  function allowance(address owner, address guy) external returns (uint256) {
    return allowance[owner][guy];
  }

  fallback() external payable {
    balanceOf[msg.sender] = ${Expr.binary (.add uint256Int .wrapping)
      (.storage (balanceOfRef sender)) (.env .callvalue)};
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.WETH9.contract := by rfl

end Benchmarks.WETH9.Syntax
