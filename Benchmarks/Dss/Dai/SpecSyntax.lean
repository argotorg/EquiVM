import Benchmarks.Dss.Dai.Spec
import Solm.Notation

/-!
# Dai spec in the Solidity-faithful Solm frontend

The whole Dai benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/Dss/Dai/Spec.lean`.

Notes:
* The strict-`&&` allowance guards are the spec's short-circuit ternaries, written as `c ? a : false`.
* `abi.encodePacked` operands carry their ABI types as `T(e)` annotations; inner casts nest, e.g.
  `uint256(uint256(holder))` is the pair `(uint256, .cast holder uint256St)`.
* `permit`'s ecrecover precompile call targets `address(1)` (a cast), which the surface low-level
  call cannot express, so that one statement is spliced; its `ecrecoverSuccess`/`ecrecoverData`
  binders are then referenced via `${…}`.  The EIP-191 `"\x19\x01"` prefix and `PERMIT_TYPEHASH`
  literal reuse the spec's `eip191Prefix`/`permitTypehashExpr` defs.
* Transition order matches `contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace Benchmarks.Dss.Dai.Syntax

def contractSyntax : ContractDecl := solidity% contract Dai {
  mapping(address => uint256) wards;
  uint256 totalSupply;
  mapping(address => uint256) balanceOf;
  mapping(address => mapping(address => uint256)) allowance;
  mapping(address => uint256) nonces;
  bytes32 DOMAIN_SEPARATOR;

  constructor(uint256 chainId_) {
    wards[msg.sender] = 1;
    DOMAIN_SEPARATOR = keccak256(abi.encodePacked(
      bytes32(keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)")),
      bytes32(keccak256("Dai Stablecoin")),
      bytes32(keccak256("1")),
      uint256(chainId_),
      uint256(uint256(this))));
  }

  function allowance(address arg0, address arg1) external returns (uint256) {
    return allowance[arg0][arg1];
  }

  function approve(address usr, uint256 wad) external returns (bool) {
    allowance[msg.sender][usr] = wad;
    return true;
  }

  function balanceOf(address arg0) external returns (uint256) {
    return balanceOf[arg0];
  }

  function burn(address usr, uint256 wad) external {
    require(balanceOf[usr] >= wad);
    if (usr != msg.sender ? allowance[usr][msg.sender] != type(uint256).max : false) {
      require(allowance[usr][msg.sender] >= wad);
      require(((allowance[usr][msg.sender] - wad) as uint256) <= allowance[usr][msg.sender]);
      allowance[usr][msg.sender] = (allowance[usr][msg.sender] - wad) as uint256;
    }
    require(balanceOf[usr] >= wad);
    require(((balanceOf[usr] - wad) as uint256) <= balanceOf[usr]);
    balanceOf[usr] = (balanceOf[usr] - wad) as uint256;
    require(((totalSupply - wad) as uint256) <= totalSupply);
    totalSupply = (totalSupply - wad) as uint256;
  }

  function decimals() external returns (uint8) {
    return 18;
  }

  function deny(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 0;
  }

  function DOMAIN_SEPARATOR() external returns (bytes32) {
    return DOMAIN_SEPARATOR;
  }

  function mint(address usr, uint256 wad) external {
    require(wards[msg.sender] == 1);
    require(((balanceOf[usr] + wad) as uint256) >= balanceOf[usr]);
    balanceOf[usr] = (balanceOf[usr] + wad) as uint256;
    require(((totalSupply + wad) as uint256) >= totalSupply);
    totalSupply = (totalSupply + wad) as uint256;
  }

  function move(address src, address dst, uint256 wad) external {
    var _ok = transferFrom(src, dst, wad);
  }

  function name() external returns (string) {
    return "Dai Stablecoin";
  }

  function nonces(address arg0) external returns (uint256) {
    return nonces[arg0];
  }

  function permit(address holder, address spender, uint256 nonce, uint256 expiry,
      bool allowed, uint8 v, bytes32 r, bytes32 s) external {
    bytes32 digest = keccak256(abi.encodePacked(
      bytes(${eip191Prefix}),
      bytes32(DOMAIN_SEPARATOR),
      bytes32(keccak256(abi.encodePacked(
        bytes32(${permitTypehashExpr}),
        uint256(uint256(holder)),
        uint256(uint256(spender)),
        uint256(nonce),
        uint256(expiry),
        uint256(allowed ? 1 : 0))))));
    require(holder != address(0));
    ${[Stmt.lowLevelCall ecrecoverPrecompile (.intLit 0) ecrecoverCalldataExpr
        "ecrecoverSuccess" "ecrecoverData" false]}
    require(${Expr.var "ecrecoverSuccess"});
    address recovered = abi.decode(${Expr.var "ecrecoverData"}, (address));
    require(holder == recovered);
    require(expiry == 0 || block.timestamp <= expiry);
    require(nonce == nonces[holder]);
    nonces[holder] = nonces[holder] + 1;
    uint256 wad = allowed ? type(uint256).max : 0;
    allowance[holder][spender] = wad;
  }

  function PERMIT_TYPEHASH() external returns (bytes32) {
    return ${permitTypehashExpr};
  }

  function pull(address usr, uint256 wad) external {
    var _ok = transferFrom(usr, msg.sender, wad);
  }

  function push(address usr, uint256 wad) external {
    var _ok = transferFrom(msg.sender, usr, wad);
  }

  function rely(address guy) external {
    require(wards[msg.sender] == 1);
    wards[guy] = 1;
  }

  function symbol() external returns (string) {
    return "DAI";
  }

  function totalSupply() external returns (uint256) {
    return totalSupply;
  }

  function transfer(address dst, uint256 wad) external returns (bool) {
    var _ok = transferFrom(msg.sender, dst, wad);
    return _ok;
  }

  function transferFrom(address src, address dst, uint256 wad) external returns (bool) {
    require(balanceOf[src] >= wad);
    if (src != msg.sender ? allowance[src][msg.sender] != type(uint256).max : false) {
      require(allowance[src][msg.sender] >= wad);
      require(((allowance[src][msg.sender] - wad) as uint256) <= allowance[src][msg.sender]);
      allowance[src][msg.sender] = (allowance[src][msg.sender] - wad) as uint256;
    }
    require(balanceOf[src] >= wad);
    require(((balanceOf[src] - wad) as uint256) <= balanceOf[src]);
    balanceOf[src] = (balanceOf[src] - wad) as uint256;
    require(((balanceOf[dst] + wad) as uint256) >= balanceOf[dst]);
    balanceOf[dst] = (balanceOf[dst] + wad) as uint256;
    return true;
  }

  function version() external returns (string) {
    return "1";
  }

  function wards(address arg0) external returns (uint256) {
    return wards[arg0];
  }
}

theorem contractSyntax_eq : contractSyntax = Benchmarks.Dss.Dai.contract := by rfl

end Benchmarks.Dss.Dai.Syntax
