// SPDX-License-Identifier: AGPL-3.0-only
// Compiled with the OPTIMIZER ON (this is the realistic target):
//   solc --optimize --evm-version shanghai --metadata-hash none --bin --bin-runtime Benchmarks/ERC721/ERC721.sol
// (solc 0.8.35, Shanghai => PUSH0).  Runtime bytecode + selector/jump facts live in Bytecode.lean.
//
// Solmate-style ERC721 *core* (IERC721 transfer/approval/ownership surface).  Deliberately omits:
//   * the ERC721Metadata extension (name/symbol/tokenURI): `string` ABI returns are not yet
//     encodable by the Solm equivalence machinery;
//   * `safeTransferFrom`: outside this compact source-level benchmark;
//   * ERC165 `supportsInterface(bytes4)`: needs a fixed-bytes (`bytes4`) literal compare.
pragma solidity ^0.8.20;

contract ERC721 {
    mapping(uint256 => address) internal _ownerOf;                       // slot 0
    mapping(address => uint256) internal _balanceOf;                     // slot 1
    mapping(uint256 => address) public getApproved;                      // slot 2
    mapping(address => mapping(address => bool)) public isApprovedForAll; // slot 3

    function ownerOf(uint256 id) public view returns (address owner) {
        require((owner = _ownerOf[id]) != address(0), "NOT_MINTED");
    }

    function balanceOf(address owner) public view returns (uint256) {
        require(owner != address(0), "ZERO_ADDRESS");
        return _balanceOf[owner];
    }

    function approve(address spender, uint256 id) public {
        address owner = _ownerOf[id];
        require(msg.sender == owner || isApprovedForAll[owner][msg.sender], "NOT_AUTHORIZED");
        getApproved[id] = spender;
    }

    function setApprovalForAll(address operator, bool approved) public {
        isApprovedForAll[msg.sender][operator] = approved;
    }

    function transferFrom(address from, address to, uint256 id) public {
        require(from == _ownerOf[id], "WRONG_FROM");
        require(to != address(0), "INVALID_RECIPIENT");
        require(
            msg.sender == from || isApprovedForAll[from][msg.sender] || msg.sender == getApproved[id],
            "NOT_AUTHORIZED"
        );
        unchecked {
            _balanceOf[from]--;
            _balanceOf[to]++;
        }
        _ownerOf[id] = to;
        delete getApproved[id];
    }
}
