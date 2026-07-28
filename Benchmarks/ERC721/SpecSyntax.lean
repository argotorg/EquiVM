import Benchmarks.ERC721.Spec
import Solm.Notation

/-!
# ERC721 spec in the Solidity-faithful Solm frontend

The whole ERC721 benchmark spec, written with `solidity%` and proven definitionally equal to the
AST spec in `Benchmarks/ERC721/Spec.lean`.

Notes mirroring the AST spec:
* The spec constructor is `{ params := [], body := [] }` — no callvalue guard — so it is written
  `payable` (which suppresses the auto guard) with an empty body.
* The `unchecked` balance decrement/increment in `transferFrom` is the explicit `% 2^256` wrap.
* `from`/`to` are Lean keywords, written `«from»`/`«to»`.
* Transition order matches `erc721Contract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace ERC721.Syntax

def contractSyntax : ContractDecl := solidity% contract ERC721 {
  mapping(uint256 => address) _ownerOf;
  mapping(address => uint256) _balanceOf;
  mapping(uint256 => address) getApproved;
  mapping(address => mapping(address => bool)) isApprovedForAll;

  constructor() payable { }

  function approve(address spender, uint256 id) external {
    address owner = _ownerOf[id];
    require(msg.sender == owner || isApprovedForAll[owner][msg.sender]);
    getApproved[id] = spender;
  }

  function balanceOf(address owner) external returns (uint256) {
    require(owner != address(0));
    return _balanceOf[owner];
  }

  function getApproved(uint256 id) external returns (address) {
    return getApproved[id];
  }

  function isApprovedForAll(address owner, address operator) external returns (bool) {
    return isApprovedForAll[owner][operator];
  }

  function ownerOf(uint256 id) external returns (address) {
    address owner = _ownerOf[id];
    require(owner != address(0));
    return owner;
  }

  function setApprovalForAll(address operator, bool approved) external {
    isApprovedForAll[msg.sender][operator] = approved;
  }

  function transferFrom(address «from», address «to», uint256 id) external {
    require(«from» == _ownerOf[id]);
    require(«to» != address(0));
    require((msg.sender == «from» || isApprovedForAll[«from»][msg.sender])
      || msg.sender == getApproved[id]);
    _balanceOf[«from»] = (_balanceOf[«from»] - 1) % #(Int.ofNat EVM.wordModulus);
    _balanceOf[«to»] = (_balanceOf[«to»] + 1) % #(Int.ofNat EVM.wordModulus);
    _ownerOf[id] = «to»;
    delete getApproved[id];
  }
}

theorem contractSyntax_eq : contractSyntax = ERC721.erc721Contract := by rfl

end ERC721.Syntax
